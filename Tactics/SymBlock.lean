/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Alex Keizer
-/
import Arm.Exec
import Arm.Memory.MemoryProofs
import Tactics.FetchAndDecode
import Tactics.Sym.Context
import Tactics.Sym

import Lean

open BitVec
open Lean
open Lean.Meta Lean.Elab.Tactic

open AxEffects SymContext
open Sym (withTraceNode withInfoTraceNode traceHeartbeats)

/-- `init_next_block h_run blocki_eq sn block_size steps_left` splits the hypothesis
  `h_run: s_final = run (n + block_size) s`
by adding a new state variable, `sn`, and two new hypotheses:
  `blocki_eq : run block_size s = s_next`
  `h_run'   : s_final = run n s_next`
to the local context of the main goal.
The names are obtained from the respectively named arguments to the tactic -/
macro "init_next_block" h_run:ident blocki_eq:ident sn:ident block_size:num steps_left:num : tactic =>
  `(tactic|
    (-- use `let` over `obtain` to prevent `.intro` goal tags
     let ⟨$sn:ident, ⟨$blocki_eq:ident, h_run_new⟩⟩ :=
      @run_oneblock _ _ $block_size:num $steps_left:num $h_run:ident
     replace $h_run:ident := h_run_new
     clear h_run_new
    ))

section blockiTac

/-- Apply the relevant pre-generated block lemma to an expression
  `blocki_eq : run ?n ?s = ?s'`
to add a new local hypothesis in terms of `w` and `write_mem`
  `h_block_s' : ?s' = w _ _ (w _ _ (... ?s))`
-/
def blockiTac (blockiEq : Expr) (hBlock : Name) : SymReaderM Unit := fun ctx =>
  withMainContext' <|
  withInfoTraceNode m!"blockiTac: {blockiEq}\n {ctx.runSteps?} {ctx.effects}" (tag := "blockiTac") <| do
    let pc := (Nat.toDigits 16 ctx.pc.toNat).asString
    --  ^^ The PC in hex
    let blockiLemma := Name.str ctx.program s!"blocki_eq_0x{pc}"
    let eff := ctx.effects
    let hStepExpr ← mkEqTrans
      (← mkEqSymm blockiEq)
      (← mkAppM blockiLemma #[
        eff.programProof,
        (← eff.getField .PC).proof,
        (← eff.getField .ERR).proof
      ])

    let goal ← getMainGoal
    let ⟨_, goal⟩ ← goal.note hBlock hStepExpr
    replaceMainGoal [goal]

end blockiTac

/--
Symbolically simulate a single step, according the the symbolic simulation
context `c`, returning the context for the next step in simulation. -/
def sym_block1 (blockSize stepsLeft : Nat) : SymM Unit := do
  /- `withCurrHeartbeats` sets the initial heartbeats to the current heartbeats,
  effectively resetting our heartbeat budget back to the maximum. -/
  withCurrHeartbeats <| do

  let stateNumber ← getCurrentStateNumber
  withTraceNode m!"(sym_block1): simulating block {stateNumber}" (tag:="sym_block1") <|
  withMainContext' do
    withInfoTraceNode "verbose context" (tag := "infoDump") <| do
      traceSymContext
      trace[Tactic.sym.info] "Goal state:\n {← getMainGoal}"

    let blocki_eq := Lean.mkIdent (.mkSimple s!"blocki_{← getCurrentStateName}")
    let h_block   := Lean.mkIdent (.mkSimple s!"h_block_{stateNumber + blockSize}")

    -- unfoldRun (fun _ => evalTacticAndTrace whileTac)

    -- Add new state to local context
    withTraceNode "initNextBlock" (tag := "initNextBlock") <| do
      let hRunId      := mkIdent <|← getHRunName
      let nextStateId := mkIdent <|← getNextStateName blockSize
      let block_size : TSyntax `num := quote blockSize
      let steps_left : TSyntax `num := quote stepsLeft
      evalTacticAndTrace <|← `(tactic|
        init_next_block $hRunId:ident $blocki_eq:ident $nextStateId:ident $block_size:num $steps_left:num
      )

    -- Apply relevant pre-generated `blocki` lemma
    withMainContext' <| do
      let blockiEq ← SymContext.findFromUserName blocki_eq.getId
      blockiTac blockiEq.toExpr h_block.getId

    -- WORKAROUND: eventually we'd like to eagerly simp away `if`s in the
    -- pre-generation of instruction semantics. For now, though, we keep a
    -- `simp` here
    withMainContext' <| do
      let hStep ← SymContext.findFromUserName h_block.getId

      -- If we know SP is aligned, `simp` with that fact
      if let some hSp := (← getThe AxEffects).stackAlignmentProof? then
        let msg := m!"simplifying {hStep.toExpr} with {hSp}"
        withTraceNode msg (tag := "simplifyHStep") <| do
          let some goal ← do
              let (ctx, simprocs) ← LNSymSimpContext
                (config := {decide := false}) (exprs := #[hSp])
              let goal ← getMainGoal
              LNSymSimp goal ctx simprocs hStep.fvarId
            | throwError "internal error: simp closed goal unexpectedly"
          replaceMainGoal [goal]
      else
        trace[Tactic.sym.info] "we have no relevant local hypotheses, \
          skipping simplification step"

    -- Prepare `h_program`,`h_err`,`h_pc`, etc. for next state
    withMainContext' <| do
      let hBlock ← SymContext.findFromUserName h_block.getId
      -- ^^ we can't reuse `hBlock` from before, since its fvarId might've been
      --    changed by `simp`
      explodeStep hBlock.toExpr blockSize
      prepareForNextStep blockSize

      let goal ← getMainGoal
      let goal ← goal.clear hBlock.fvarId
      replaceMainGoal [goal]
      trace[Tactic.sym.info] "CurrentStateNumber: {← getCurrentStateNumber}"
      trace[Tactic.sym.info] "CurrentState: {← getCurrentState}"
      trace[Tactic.sym.info] "CurrentStateName: {← getCurrentStateName}"
      traceHeartbeats

syntax sym_block_size := "(" "block_size" " := " num ")"
syntax sym_block_sizes := "(" "block_sizes" " := " "[" num,* "]" ")"

/--
Get the first `n` elements of the list `xs`, where `acc` is the accumulator.

(FIXME) Implicit assumption: `xs` has at least one assumption.
-/
def first_n (n : Nat) (xs acc : List Nat) : List Nat :=
  match n with
  | 0 => acc.reverse
  | n' + 1 => first_n n' xs.tail (List.headD xs 0 :: acc)

/-- info: 5 -/
#guard_msgs in
#eval (first_n 1 [5, 2, 2, 1] []).foldl Nat.add 0

open Elab.Term (elabTerm) in
elab "sym_block" n:num
                 -- block_size:(sym_block_size)?
                 block_sizes:(sym_block_sizes)?
                 s:(sym_at)? : tactic => do
  traceHeartbeats "initial heartbeats"

  let s ← s.mapM fun
    | `(sym_at|at $s:ident) => pure s.getId
    | _ => Lean.Elab.throwUnsupportedSyntax
  let block_sizes ← block_sizes.mapM (fun
  | `(sym_block_sizes|(block_sizes := [$elems,*])) => do
      let size_exprs ← elems.getElems.mapM (fun elem => do
        let size := elem.getNat
        return (mkNatLit size))
      let size_terms ← size_exprs.mapM (fun e => do
          let some val ← Lean.Meta.getNatValue? e | throwError ""
          return val)      
      pure size_terms.toList
  |  _ =>
      -- (FIXME)
      -- If no block size is specified, we step one instruction at a time.
      pure [1])
  let block_sizes := block_sizes.get!
  trace[Tactic.sym.info] "block_sizes: {block_sizes}"

  -- let block_size ← block_size.mapM (fun
  -- | `(sym_block_size|(block_size := $val)) => pure val.getNat
  -- |  _ => -- If no block size is specified, we step one instruction at a time.
  --         pure 1)
  -- let block_size := block_size.get!

  let c ← SymContext.fromMainContext s
  -- TODO: Is this `get!` safe?
  -- let total_steps := c.runSteps?.get!
  -- The number of instructions, not blocks, the user asked to simulate.
  let sim_steps := n.getNat
  -- We compute the number of blocks to be simulated using a ceiling divide.
  -- Note that the last block can be < `block_size`.
  -- let num_blocks := (sim_steps + block_size - 1) / block_size

  SymM.run' c <| withMainContext' <|  do
    -- Check pre-conditions
    -- TODO
    -- assertStepTheoremsGenerated
    -- let n ← ensureAtMostRunSteps n.getNat

    withMainContext' <| do
      -- The main loop
      -- for i in List.range num_blocks do
      --   let block_size' := min (sim_steps - (i * block_size)) block_size
      --   let steps_left := (total_steps - (i * block_size) - block_size')
      --   sym_block1 block_size' steps_left
      let mut ctr := 0
      for bsize in block_sizes do
        ctr := ctr + 1
        let steps_left := sim_steps - ((first_n ctr block_sizes []).foldl Nat.add 0)
        sym_block1 bsize steps_left

    traceHeartbeats "symbolic simulation total"
    withCurrHeartbeats <|
    withTraceNode "Post processing" (tag := "postProccessing") <| do
      let c ← getThe SymContext
      -- Check if we can substitute the final state
      if c.runSteps? = some 0 then
        let msg := do
          let hRun ← userNameToMessageData c.h_run
          pure m!"runSteps := 0, substituting along {hRun}"
        withMainContext' <|
        withTraceNode `Tactic.sym (fun _ => msg) <| do
          let sfEq ← mkEq (← getCurrentState) c.finalState

          let goal ← getMainGoal
          trace[Tactic.sym.info] "original goal:\n{goal}"
          let ⟨hEqId, goal⟩ ← do
            let hRun ← SymContext.findFromUserName c.h_run
            goal.note `this (← mkEqSymm hRun.toExpr) sfEq
          goal.withContext <| do
            trace[Tactic.sym.info] "added {← userNameToMessageData `this} of type \
              {sfEq} in:\n{goal}"

          let goal ← subst goal hEqId
          trace[Tactic.sym.info] "performed subsitutition in:\n{goal}"
          replaceMainGoal [goal]

      -- Rudimentary aggregation: we feed all the axiomatic effect hypotheses
      -- added while symbolically evaluating to `simp`
      withMainContext' <|
      withTraceNode m!"aggregating (non-)effects" (tag := "aggregateEffects") <| do
        let goal? ← LNSymSimp (← getMainGoal) c.aggregateSimpCtx c.aggregateSimprocs
        replaceMainGoal goal?.toList

      traceHeartbeats "aggregation"

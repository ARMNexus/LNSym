/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Siddharth Bhat

In this file, we define proof automation for separation conditions of memory.

References:
- https://github.com/leanprover/lean4/blob/240ebff549a2cf557f9abe9568f5de885f13e50d/src/Lean/Elab/Tactic/Omega/OmegaM.lean
- https://github.com/leanprover/lean4/blob/240ebff549a2cf557f9abe9568f5de885f13e50d/src/Lean/Elab/Tactic/Omega/Frontend.lean
-/
import Arm
import Arm.Memory.MemoryProofs
import Arm.BitVec
import Arm.Memory.Attr
import Arm.Memory.AddressNormalization
import Lean
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Rewrites
import Lean.Elab.Tactic.Conv
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Conv.Basic
import Tactics.Simp
import Tactics.BvOmegaBench
import Arm.Memory.Common

open Lean Meta Elab Tactic Memory

namespace MemOmega

/--
A user given hypothesis for mem_omega, which we process as either a hypothesis (FVarId),
or a term that is added into the user's context.
-/
inductive UserHyp
| hyp : FVarId → UserHyp
| star : UserHyp
| excludeHyp : FVarId → UserHyp
| expr : Expr → UserHyp

namespace UserHyp
def ofExpr (e : Expr) : UserHyp := 
  if e.isFVar then
    .hyp e.fvarId!
  else 
    .expr e
end UserHyp


structure Config where
  /--
    If true, then MemOmega will explode uses of pairwiseSeparate [mem₁, ... memₙ]
    into O(n^2) separation conditions.
  -/
  explodePairwiseSeparate : Bool := false

/-- Edit the config for mem_omega! -/
def Config.mkBang (c : Config) : Config :=
  { c with explodePairwiseSeparate := true }

/-- Context for the `SimpMemM` monad, containing the user configurable options. -/
structure Context where
  /-- User configurable options for `simp_mem`. -/
  cfg : Config
  /--
  If we are using `mem_omega only [...]`, then we will have `some` plus the hyps.
  If we are using `mem_omega`, then we will get `none`.
  -/
  userHyps? : Option (Array UserHyp)
  /-- Cache of `bv_toNat` simp context. -/
  bvToNatSimpCtx : Simp.Context
  /-- Cache of `bv_toNat` simprocs. -/
  bvToNatSimprocs : Array Simp.Simprocs


namespace Context

def init (cfg : Config) (userHyps? : Option (Array UserHyp)) : MetaM Context := do
  let (bvToNatSimpCtx, bvToNatSimprocs) ←
    LNSymSimpContext
      (config := {failIfUnchanged := false})
      -- Also use `mem_{legal', subset', separate'}.iff_omega to unfold definitions that
      -- occur inside compound expressions, such as (mem_subset' .. ∨ mem_subset' ..)
      -- (thms := #[``mem_legal'.iff_omega, ``mem_subset'.iff_omega, ``mem_separate'.iff_omega])
      (simp_attrs := #[`bv_toNat])
      (useDefaultSimprocs := false)
  return {cfg, bvToNatSimpCtx, bvToNatSimprocs, userHyps? }
end Context

abbrev MemOmegaM := (ReaderT Context MetaM)

namespace MemOmegaM
  def run (ctx : Context) (x : MemOmegaM α) : MetaM α := ReaderT.run x ctx
end MemOmegaM

/-- Modify the set of hypotheses `hyp` based on the user hyp `hyp`. -/
def mkKeepHypsOfUserHyp (g : MVarId) (set : Std.HashSet FVarId) (hyp : UserHyp) : MetaM <| Std.HashSet FVarId :=
  match hyp with 
  | .hyp fvar => return set.insert fvar
  | .excludeHyp fvar => return set.erase fvar
  | .star => do 
     let allHyps ← g.getNondepPropHyps
     return allHyps.foldl (init := set) (fun s fvar => s.insert fvar)
  | .expr _e => return set

/--
Fold over the array of `UserHyps`, build tracking `FVarId`s for the ones that we use.
if the array is `.none`, then we keep everything. 
-/
def mkKeepHypsOfUserHyps (g : MVarId) (userHyps? : Option (Array UserHyp)) : MetaM <| Std.HashSet FVarId :=
  (userHyps?.getD #[]).foldlM (init := ∅) (MemOmega.mkKeepHypsOfUserHyp g)

/-- Fold over the array of `UserHyps`, build tracking `FVarId`s for the ones that we use.
if the array is `.none`, then we keep everything. 
This partitions `userHyps` into the ones that create `Memory.Hypothesis`, and the ones that we leave as `FVarId`s,
which may contain memory assumptions that we cannot translate (eg. bounds like `b - a ≤ 200`.)
-/
def mkMemoryAndKeepHypsOfUserHyps (g : MVarId) (userHyps? : Option (Array UserHyp)) : MetaM <| Array Memory.Hypothesis × Array FVarId := do 
  let keepHyps : Std.HashSet FVarId ← mkKeepHypsOfUserHyps g userHyps?
  g.withContext do
    let mut foundHyps : Array Memory.Hypothesis := #[]
    let mut nonmem := #[]
    for h in keepHyps do
      let sz := foundHyps.size
      foundHyps ← hypothesisOfExpr (Expr.fvar h) foundHyps
      if foundHyps.size == sz then 
        -- size did not change, so that was a non memory hyp.
        nonmem := nonmem.push h
    return (foundHyps, nonmem)
  
  

def memOmega (g : MVarId) : MemOmegaM Unit := do
    g.withContext do
      let rawHyps ← getLocalHyps
      let mut hyps := #[]
      -- extract out structed values for all hyps.
      for h in rawHyps do
        hyps ← hypothesisOfExpr h hyps

      -- only enable pairwise constraints if it is enabled.
      let isPairwiseEnabled := (← readThe Context).cfg.explodePairwiseSeparate
      hyps := hyps.filter (!·.isPairwiseSeparate || isPairwiseEnabled)

      -- used specialized procedure that doesn't unfold everything for the easy case.
      if ← closeMemSideCondition g (← readThe Context).bvToNatSimpCtx (← readThe Context).bvToNatSimprocs hyps then
        return ()
      else
        -- in the bad case, just rip through everything.
        let (_, g) ← Hypothesis.addOmegaFactsOfHyps g hyps.toList #[]

        TacticM.withTraceNode' m!"Reducion to omega" do
          try
            TacticM.traceLargeMsg m!"goal (Note: can be large)"  m!"{g}"
            omega g ((← g.getNondepPropHyps).map Expr.fvar) (← readThe Context).bvToNatSimpCtx (← readThe Context).bvToNatSimprocs
            trace[simp_mem.info] "{checkEmoji} `omega` succeeded."
          catch e =>
            trace[simp_mem.info]  "{crossEmoji} `omega` failed with error:\n{e.toMessageData}"
            throw e

def memOmegaWithHyps (g : MVarId) (rawHyps : Array FVarId) : MemOmegaM Unit := do
    g.withContext do
      let mut hyps := #[]
      -- extract out structed values for all hyps.
      for h in rawHyps do
        hyps ← hypothesisOfExpr (.fvar h) hyps

      -- only enable pairwise constraints if it is enabled.
      let isPairwiseEnabled := (← readThe Context).cfg.explodePairwiseSeparate
      hyps := hyps.filter (!·.isPairwiseSeparate || isPairwiseEnabled)

      -- used specialized procedure that doesn't unfold everything for the easy case.
      if ← closeMemSideCondition g (← readThe Context).bvToNatSimpCtx (← readThe Context).bvToNatSimprocs hyps then
        return ()
      else
        -- in the bad case, just rip through everything.
        let (_, g) ← Hypothesis.addOmegaFactsOfHyps g hyps.toList #[]

        TacticM.withTraceNode' m!"Reducion to omega" do
          try
            TacticM.traceLargeMsg m!"goal (Note: can be large)"  m!"{g}"
            omega g (← getLCtx).getFVars (← readThe Context).bvToNatSimpCtx (← readThe Context).bvToNatSimprocs
            trace[simp_mem.info] "{checkEmoji} `omega` succeeded."
          catch e =>
            trace[simp_mem.info]  "{crossEmoji} `omega` failed with error:\n{e.toMessageData}"
            throw e

-- syntax memOmegaRule := term

/--
Allow elaboration of `MemOmegaConfig` arguments to tactics.
-/
declare_config_elab elabMemOmegaConfig MemOmega.Config

syntax userHyp := (&"-")? term <|> Parser.Tactic.locationWildcard

syntax memOmegaWith := &"with" "[" withoutPosition(userHyp,*,?) "]"

/--
Implement the `mem_omega` tactic, which unfolds information about memory and then closes the goal state using `omega`.
-/
syntax (name := mem_omega) "mem_omega" (Lean.Parser.Tactic.config)? (memOmegaWith)?  : tactic

/--
Implement the `mem_omega` tactic frontend.
-/
syntax (name := mem_omega_bang) "mem_omega!" (memOmegaWith)?  : tactic

-- /-- Since we have
-- syntax memOmegaRule := term
-- 
-- it is safe to coerce a UserHyp into a `term`.
-- -/
-- def UserHyp.toTermSyntax (t : TSyntax ``MemOmega.memOmegaRule) : TSyntax `term :=
--   TSyntax.mk t.raw
  

/--
build a `UserHyp` from the raw syntax.
This supports using fars, using CDot notation to partially apply theorems, and to use terms.

Adapted from Lean.Elab.Tactic.Rw.WithRWRulesSeq, Lean.Elab.Tactic.Simp.resolveSimpIdTheorem, Lean.Elab.Tactic.Simp.addSimpTheorem
-/
def UserHyp.ofTerm (t : TSyntax `term) : TacticM UserHyp := do
  -- See if we can interpret `id` as a hypothesis first.
  if let .some fvarId ← optional <| getFVarId t then
    return .hyp fvarId
  else if let some e ← Term.elabCDotFunctionAlias? t then
    return .expr e
  else 
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    let e := e.eta
    if e.hasMVar then
      throwErrorAt t "found metavariables when elaborating rule, giving up."
    return .expr e

open memOmega in
def UserHyp.ofSyntax (stx : TSyntax `MemOmega.userHyp) : TacticM UserHyp :=
  let arg := stx.raw[1]
  if arg.getKind == ``Parser.Tactic.locationWildcard then
    return .star
  else 
    match stx with
    | `(userHyp| $t:term) => UserHyp.ofTerm t
    | `(userHyp| -$t:term) =>  do
        if let .some fvarId ← optional <| getFVarId t then
          return .excludeHyp fvarId
        throwError "Cannot exclude non-hypothesis '{t}'."
    | stx => do  
        throwError "Cannot parse user hypothesis '{stx}'."

-- Adapted from WithRWRulesSeq.
def elabMemOmegaWith : TSyntax ``MemOmega.memOmegaWith → TacticM (Array UserHyp) 
| `(memOmegaWith| with [ $[ $rules],* ]) =>  do
    rules.mapM UserHyp.ofSyntax
| _ => throwUnsupportedSyntax

open Lean.Parser.Tactic in
@[tactic mem_omega]
def evalMemOmega : Tactic := fun 
  | `(tactic| mem_omega $[$cfg:config]? $[$v:memOmegaWith]?) => do
    let cfg ← elabMemOmegaConfig (mkOptionalNode cfg)
    let memOmegaRules? := ← v.mapM elabMemOmegaWith
    liftMetaFinishingTactic fun g => do
      memOmega g |>.run (← Context.init cfg memOmegaRules?)
  | _ => throwUnsupportedSyntax

@[tactic mem_omega_bang]
def evalMemOmegaBang : Tactic := fun
  | `(tactic| mem_omega! $[$cfg]?) => do
    let cfg ← elabMemOmegaConfig (mkOptionalNode cfg)
    liftMetaFinishingTactic fun g => do
      memOmega g |>.run (← Context.init cfg.mkBang .none)
  | _ => throwUnsupportedSyntax

end MemOmega

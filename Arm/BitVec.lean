/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Siddharth Bhat, Alex Keizer
-/

/- Kitchen sink file for bitvector theorems -/

----------------------------------------------------------------------

import Arm.Attr

namespace BitVec

open BitVec

attribute [local ext] BitVec
/--
info: BitVec.ext_iff {w : Nat} {x y : BitVec w} : x = y ↔ x.toFin = y.toFin
-/
#guard_msgs in
#check BitVec.ext_iff

def unsigned_compare (a b : BitVec n) : Ordering :=
  if BitVec.ult a b then .lt else if a = b then .eq else .gt

instance : Ord (BitVec n) where
  -- Unsigned comparison
  compare := unsigned_compare

instance {w} : Hashable (BitVec w) where
  hash x := hash x.toNat

-- Adding some useful simp lemmas to `bitvec_rules`: we do not include
-- `bv_toNat` lemmas here.
-- See Init.Data.BitVec.Lemmas.
attribute [bitvec_rules] BitVec.ofFin_eq_ofNat
attribute [bitvec_rules] BitVec.ofFin.injEq
attribute [bitvec_rules] BitVec.cast_eq
attribute [bitvec_rules] BitVec.setWidth_eq
attribute [bitvec_rules] BitVec.getLsbD_ofFin
attribute [bitvec_rules] BitVec.getLsbD_ge
attribute [bitvec_rules] BitVec.getMsbD_ge
attribute [bitvec_rules] BitVec.toNat_zero_length
attribute [bitvec_rules] BitVec.getLsbD_zero_length
attribute [bitvec_rules] BitVec.getMsbD_zero_length
attribute [bitvec_rules] BitVec.msb_zero_length
attribute [bitvec_rules] BitVec.toNat_ofBool
attribute [bitvec_rules] BitVec.msb_ofBool
attribute [bitvec_rules] BitVec.not_ofBool
attribute [bitvec_rules] BitVec.toNat_ofFin
attribute [bitvec_rules] BitVec.toNat_ofNatLt
attribute [bitvec_rules] BitVec.getLsbD_ofNatLt
attribute [bitvec_rules] BitVec.toFin_ofNat
attribute [bitvec_rules] BitVec.getLsbD_zero
attribute [bitvec_rules] BitVec.getMsbD_zero
attribute [bitvec_rules] BitVec.toNat_mod_cancel
attribute [bitvec_rules] BitVec.msb_zero
attribute [bitvec_rules] BitVec.toNat_cast
attribute [bitvec_rules] BitVec.getLsbD_cast
attribute [bitvec_rules] BitVec.getMsbD_cast
-- attribute [bitvec_rules] BitVec.toNat_ofInt -- TODO: not tagged bv_toNat.
attribute [bv_toNat] BitVec.toNat_ofInt
attribute [bitvec_rules] BitVec.toInt_ofInt
attribute [bitvec_rules] BitVec.ofInt_natCast
attribute [bitvec_rules] BitVec.ofNat_toNat

/-! ### setWidth / truncate / zeroExtend -/

-- We adopt `setWidth` as the simp normal form
attribute [bitvec_rules] BitVec.truncate_eq_setWidth
attribute [bitvec_rules] BitVec.zeroExtend_eq_setWidth

attribute [bitvec_rules] BitVec.toNat_setWidth'
attribute [bitvec_rules] BitVec.setWidth_zero
attribute [bitvec_rules] BitVec.getLsbD_setWidth'
attribute [bitvec_rules] BitVec.getLsbD_setWidth
attribute [bitvec_rules] BitVec.getMsbD_setWidth'
attribute [bitvec_rules] BitVec.getMsbD_setWidth_add
attribute [bitvec_rules] BitVec.setWidth_setWidth_of_le
attribute [bitvec_rules] BitVec.setWidth_cast

attribute [bitvec_rules] BitVec.extractLsb_ofFin
attribute [bitvec_rules] BitVec.extractLsb_ofNat
attribute [bitvec_rules] BitVec.extractLsb'_toNat
attribute [bitvec_rules] BitVec.extractLsb_toNat
attribute [bitvec_rules] BitVec.getLsbD_extract
attribute [bitvec_rules] BitVec.toNat_allOnes
attribute [bitvec_rules] BitVec.getLsbD_allOnes
attribute [bitvec_rules] BitVec.toNat_or
attribute [bitvec_rules] BitVec.toFin_or
attribute [bitvec_rules] BitVec.getLsbD_or
attribute [bitvec_rules] BitVec.getMsbD_or
attribute [bitvec_rules] BitVec.msb_or
attribute [bitvec_rules] BitVec.setWidth_or
attribute [bitvec_rules] BitVec.toNat_and
attribute [bitvec_rules] BitVec.toFin_and
attribute [bitvec_rules] BitVec.getLsbD_and
attribute [bitvec_rules] BitVec.getMsbD_and
attribute [bitvec_rules] BitVec.msb_and
attribute [bitvec_rules] BitVec.setWidth_and
attribute [bitvec_rules] BitVec.toNat_xor
attribute [bitvec_rules] BitVec.toFin_xor
attribute [bitvec_rules] BitVec.getLsbD_xor
attribute [bitvec_rules] BitVec.setWidth_xor
-- attribute [bitvec_rules] BitVec.toNat_not
attribute [bitvec_rules] BitVec.toFin_not
attribute [bitvec_rules] BitVec.getLsbD_not
attribute [bitvec_rules] BitVec.setWidth_not
attribute [bitvec_rules] BitVec.not_cast
attribute [bitvec_rules] BitVec.and_cast
attribute [bitvec_rules] BitVec.or_cast
attribute [bitvec_rules] BitVec.xor_cast
-- attribute [bitvec_rules] BitVec.toNat_shiftLeft
attribute [bitvec_rules] BitVec.toFin_shiftLeft
attribute [bitvec_rules] BitVec.getLsbD_shiftLeft
attribute [bitvec_rules] BitVec.getMsbD_shiftLeft
attribute [bitvec_rules] BitVec.getLsbD_shiftLeftZeroExtend
attribute [bitvec_rules] BitVec.getMsbD_shiftLeftZeroExtend
attribute [bitvec_rules] BitVec.msb_shiftLeftZeroExtend
attribute [bitvec_rules] BitVec.toNat_ushiftRight
attribute [bitvec_rules] BitVec.getLsbD_ushiftRight
attribute [bitvec_rules] BitVec.toNat_append
attribute [bitvec_rules] BitVec.getLsbD_append
attribute [bitvec_rules] BitVec.getMsbD_append
attribute [bitvec_rules] BitVec.setWidth_append
attribute [bitvec_rules] BitVec.setWidth_cons
attribute [bitvec_rules] BitVec.not_append
attribute [bitvec_rules] BitVec.and_append
attribute [bitvec_rules] BitVec.or_append
attribute [bitvec_rules] BitVec.xor_append
attribute [bitvec_rules] BitVec.toNat_cons
attribute [bitvec_rules] BitVec.getLsbD_cons
attribute [bitvec_rules] BitVec.msb_cons
attribute [bitvec_rules] BitVec.getMsbD_cons_zero
attribute [bitvec_rules] BitVec.getMsbD_cons_succ
attribute [bitvec_rules] BitVec.not_cons
attribute [bitvec_rules] BitVec.cons_or_cons
attribute [bitvec_rules] BitVec.cons_and_cons
attribute [bitvec_rules] BitVec.cons_xor_cons
attribute [bitvec_rules] BitVec.toNat_concat
attribute [bitvec_rules] BitVec.getLsbD_concat_zero
attribute [bitvec_rules] BitVec.getLsbD_concat_succ
attribute [bitvec_rules] BitVec.not_concat
attribute [bitvec_rules] BitVec.concat_or_concat
attribute [bitvec_rules] BitVec.concat_and_concat
attribute [bitvec_rules] BitVec.concat_xor_concat
-- attribute [bitvec_rules] BitVec.toNat_add
attribute [bitvec_rules] BitVec.toFin_add
attribute [bitvec_rules] BitVec.ofFin_add
attribute [bitvec_rules] BitVec.add_ofFin
attribute [bitvec_rules] BitVec.add_zero
attribute [bitvec_rules] BitVec.zero_add
attribute [bitvec_rules] BitVec.toInt_add
-- attribute [bitvec_rules] BitVec.toNat_sub
attribute [bv_toNat] toNat_sub
attribute [bitvec_rules] BitVec.toFin_sub
attribute [bitvec_rules] BitVec.ofFin_sub
attribute [bitvec_rules] BitVec.sub_ofFin
attribute [bitvec_rules] BitVec.sub_zero
attribute [bitvec_rules] BitVec.sub_self
-- attribute [bitvec_rules] BitVec.toNat_neg
attribute [bitvec_rules] BitVec.toFin_neg
attribute [bitvec_rules] BitVec.neg_zero
-- attribute [bitvec_rules] BitVec.toNat_mul
attribute [bitvec_rules] BitVec.toFin_mul
attribute [bitvec_rules] BitVec.mul_zero
attribute [bitvec_rules] BitVec.mul_one
attribute [bitvec_rules] BitVec.one_mul
attribute [bitvec_rules] BitVec.toInt_mul
attribute [bitvec_rules] BitVec.le_ofFin
attribute [bitvec_rules] BitVec.ofFin_le
attribute [bitvec_rules] BitVec.ofNat_le_ofNat
attribute [bitvec_rules] BitVec.lt_ofFin
attribute [bitvec_rules] BitVec.ofFin_lt
attribute [bitvec_rules] BitVec.ofNat_lt_ofNat
attribute [bitvec_rules] BitVec.rotateLeft_mod_eq_rotateLeft
attribute [bitvec_rules] BitVec.getLsbD_rotateLeft
attribute [bitvec_rules] BitVec.rotateRight_mod_eq_rotateRight
attribute [bitvec_rules] BitVec.getLsbD_rotateRight
attribute [bitvec_rules] BitVec.ofBool_true
attribute [bitvec_rules] BitVec.ofBool_false
attribute [bitvec_rules] BitVec.ofNat_eq_ofNat
attribute [bitvec_rules] BitVec.zero_eq
attribute [bitvec_rules] BitVec.zero_or
attribute [bitvec_rules] BitVec.or_zero
attribute [bitvec_rules] BitVec.or_self

attribute [bitvec_rules] BitVec.add_sub_cancel
attribute [bitvec_rules] BitVec.sub_add_cancel

-- BitVec Simproc rules:
-- See Lean/Meta/Tactic/Simp/BuiltinSimprocs for the built-in
-- simprocs.
attribute [bitvec_rules] BitVec.reduceNeg
attribute [bitvec_rules] BitVec.reduceNot
attribute [bitvec_rules] BitVec.reduceAbs
attribute [bitvec_rules] BitVec.reduceAnd
attribute [bitvec_rules] BitVec.reduceOr
attribute [bitvec_rules] BitVec.reduceXOr
attribute [bitvec_rules] BitVec.reduceAdd
attribute [bitvec_rules] BitVec.reduceMul
attribute [bitvec_rules] BitVec.reduceSub
attribute [bitvec_rules] BitVec.reduceDiv
attribute [bitvec_rules] BitVec.reduceMod
attribute [bitvec_rules] BitVec.reduceUMod
attribute [bitvec_rules] BitVec.reduceUDiv
attribute [bitvec_rules] BitVec.reduceSMTUDiv
attribute [bitvec_rules] BitVec.reduceSMod
attribute [bitvec_rules] BitVec.reduceSRem
attribute [bitvec_rules] BitVec.reduceSDiv
attribute [bitvec_rules] BitVec.reduceSMTSDiv
attribute [bitvec_rules] BitVec.reduceGetLsb
attribute [bitvec_rules] BitVec.reduceGetMsb
attribute [bitvec_rules] BitVec.reduceShiftLeft
attribute [bitvec_rules] BitVec.reduceUShiftRight
attribute [bitvec_rules] BitVec.reduceSShiftRight
attribute [bitvec_rules] BitVec.reduceHShiftLeft
attribute [bitvec_rules] BitVec.reduceHShiftLeft'
attribute [bitvec_rules] BitVec.reduceHShiftRight
attribute [bitvec_rules] BitVec.reduceHShiftRight'
attribute [bitvec_rules] BitVec.reduceRotateLeft
attribute [bitvec_rules] BitVec.reduceRotateRight
attribute [bitvec_rules] BitVec.reduceAppend
attribute [bitvec_rules] BitVec.reduceCast
attribute [bitvec_rules] BitVec.reduceToNat
attribute [bitvec_rules] BitVec.reduceToInt
attribute [bitvec_rules] BitVec.reduceOfInt
attribute [bitvec_rules] BitVec.reduceOfNat
attribute [bitvec_rules] BitVec.reduceEq
attribute [bitvec_rules] BitVec.reduceNe
attribute [bitvec_rules] BitVec.reduceLT
attribute [bitvec_rules] BitVec.reduceLE
attribute [bitvec_rules] BitVec.reduceGT
attribute [bitvec_rules] BitVec.reduceGE
attribute [bitvec_rules] BitVec.reduceULT
attribute [bitvec_rules] BitVec.reduceULE
attribute [bitvec_rules] BitVec.reduceSLT
attribute [bitvec_rules] BitVec.reduceSLE
attribute [bitvec_rules] BitVec.reduceSetWidth'
attribute [bitvec_rules] BitVec.reduceShiftLeftZeroExtend
attribute [bitvec_rules] BitVec.reduceExtracLsb'
attribute [bitvec_rules] BitVec.reduceReplicate
attribute [bitvec_rules] BitVec.reduceSetWidth
attribute [bitvec_rules] BitVec.reduceSignExtend
attribute [bitvec_rules] BitVec.reduceAllOnes
attribute [bitvec_rules] BitVec.reduceBitVecOfFin
attribute [bitvec_rules] BitVec.reduceBitVecToFin
attribute [bitvec_rules] BitVec.reduceShiftLeftShiftLeft
attribute [bitvec_rules] BitVec.reduceShiftRightShiftRight

-- BitVec/Nat Simproc rules
attribute [bitvec_rules] BitVec.reduceToNat
attribute [bitvec_rules] Nat.reduceAdd
attribute [bitvec_rules] Nat.reduceMul
attribute [bitvec_rules] Nat.reduceSub
attribute [bitvec_rules] Nat.reduceDiv
attribute [bitvec_rules] Nat.reduceMod
attribute [bitvec_rules] Nat.reducePow
attribute [bitvec_rules] Nat.reduceGcd
attribute [bitvec_rules] Nat.reduceLT
attribute [bitvec_rules] Nat.reduceGT
attribute [bitvec_rules] Nat.reduceBEq
attribute [bitvec_rules] Nat.reduceBNe
attribute [bitvec_rules] Nat.reduceEqDiff
attribute [bitvec_rules] Nat.reduceBeqDiff
attribute [bitvec_rules] Nat.reduceBneDiff
attribute [bitvec_rules] Nat.reduceLTLE
attribute [bitvec_rules] Nat.reduceLeDiff
attribute [bitvec_rules] Nat.reduceSubDiff

-- This might be a neccesary evil: it introduces a modulus,
-- but it's also really useful.
attribute [bitvec_rules] BitVec.toNat_ofNat

-- Some Fin lemmas useful for bitvector reasoning:
attribute [bitvec_rules] Fin.eta
attribute [bitvec_rules] Fin.isLt
attribute [bitvec_rules] Fin.isValue -- To normalize Fin literals

-- Some lemmas useful for clean-up after the use of simp/ground
-- leaves some terms exposed:
attribute [bitvec_rules] BitVec.val_toFin

----------------------------------------------------------------------
/-! # `BitVec` definitions used in LNSym -/

/-- Get the width of a bitvector. -/
protected def width (_ : BitVec n) : Nat := n

/-- Convert a bitvector into its hex representation, without leading zeroes.

See `BitVec.toHex` if you do want the leading zeroes.

NOTE: returns only the digits, without a `0x` prefix -/
def toHexWithoutLeadingZeroes {w} (x : BitVec w) : String :=
  (Nat.toDigits 16 x.toNat).asString

/-- `partInstall start len val x` returns a bitvector where bits
- `start` to `start+len` are equal to `val`, and
- all other bits are equal to the respective bit in `x` -/
abbrev partInstall (start len : Nat) (val : BitVec len) (x : BitVec n): BitVec n :=
  let mask := allOnes len
  let val_aligned := (zeroExtend n val) <<< start
  let mask_with_hole := ~~~ ((zeroExtend n mask) <<< start)
  let x_with_hole := x &&& mask_with_hole
  x_with_hole ||| val_aligned

example : (partInstall 0 4 0xC#4 0xAB0D#16 = 0xAB0C#16) := rfl

@[bitvec_rules]
theorem partInstall_partInstall (x : BitVec n) :
    partInstall (start + len₁) len₂ val₂ (partInstall start len₁ val₁ x)
    = (partInstall start _ (val₂ ++ val₁) x).cast (by omega) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [partInstall, truncate_eq_setWidth, getLsbD_or, getLsbD_and,
    getLsbD_not, Fin.is_lt, decide_True, getLsbD_shiftLeft, Bool.true_and,
    getLsbD_setWidth, getLsbD_allOnes, Bool.not_and, Bool.not_not,
    getLsbD_cast, BitVec.getLsbD_append]
  simp only [
    show ∀ m, i.val - m < n by omega,
    decide_True, Bool.not_true, Bool.false_or, Bool.true_and]
  by_cases h₁ : i < start
  · simp [h₁, show i < start + len₁ by omega]
  · simp only [h₁, decide_False, Bool.false_or, Bool.not_false, Bool.true_and,
      show i < start + len₁ ↔ i - start < len₁ by omega]
    by_cases h₂ : i - start < len₁
    · simp [h₂, show ↑i - start < len₂ + len₁ by omega]
    · rw [BitVec.getLsbD_ge val₁ _ (by omega)]
      simp [h₂, Nat.sub_add_eq,
        show i - start < len₂ + len₁ ↔ i - start - len₁ < len₂ by omega]

/-- `partInstall`ing at bit `0` a value `x` of the same width as the original
bitvector `y` returns exactly the value `x` -/
@[bitvec_rules]
theorem partInstall_eq (x y : BitVec n) :
    partInstall 0 n x y = x := by
  simp [partInstall]

/-- Flatten a list of bitvectors into one bitvector. -/
protected def flatten {n : Nat} (xs : List (BitVec n)) : BitVec (n * xs.length) :=
  match xs with
  | [] => 0#0
  | x :: rest =>
    have h : n + n * List.length rest = n * List.length (x :: rest) := by
      simp [List.length_cons, Nat.mul_one, Nat.mul_add, Nat.succ_eq_one_add]
      omega
    BitVec.cast h (x ++ (BitVec.flatten rest))

/-- Tail-recursive version of `BitVec.flatten`. -/
protected def flattenTR {n : Nat} (xs : List (BitVec n)) (i : Nat)
  (acc : BitVec len) (H : n > 0) : BitVec len :=
  match xs with
  | [] => acc
  | x :: rest =>
    let new_acc := (BitVec.partInstall (i * n) n x acc)
    BitVec.flattenTR rest (i + 1) new_acc H

/--
Generate a random bitvector of width n. The range of the values
can also be specified using lo and hi arguments, which default to 0
and 2^n - 1 (inclusive), respectively.
-/
protected def rand (n : Nat) (lo := 0) (hi := 2^n - 1) : IO (BitVec n) := do
  pure (BitVec.ofNat n (← IO.rand lo hi))

@[bitvec_rules]
abbrev ror (x : BitVec n) (r : Nat) : BitVec n :=
  rotateRight x r

/--
Return the `i`-th least significant bit (or `0` if `i >= w`) of
the `n`-bit bitvector `x`.
-/
@[bitvec_rules]
abbrev lsb (x : BitVec n) (i : Nat) : BitVec 1 :=
  BitVec.extractLsb' i 1 x

/-- Reverse bits of a bit-vector. -/
def reverse (x : BitVec n) : BitVec n :=
  let rec reverseTR (x : BitVec n) (i : Nat) (acc : BitVec n) :=
    match i with
    | 0 => acc
    | j + 1 =>
      let xi := extractLsb' (i - 1) 1 x
      let acc := BitVec.partInstall (n - i) 1 xi acc
      reverseTR x j acc
  reverseTR x n $ BitVec.zero n

example : reverse 0b11101#5 = 0b10111#5 := rfl

/-- Split a bit-vector `x` into sub-vectors, each of size `e`. -/
def split (x : BitVec n) (e : Nat) (h : 0 < e): List (BitVec e) :=
  let rec splitTR (x : BitVec n) (e : Nat) (h : 0 < e)
    (i : Nat) (acc : List (BitVec e)) : List (BitVec e) :=
    match i with
    | 0 => acc
    | j + 1 =>
      let lo := (n / e - i) * e
      let part : BitVec e := extractLsb' lo e x
      let newacc := part :: acc
      splitTR x e h j newacc
  splitTR x e h (n / e) []

example : split 0xabcd1234#32 8 (by omega) = [0xab#8, 0xcd#8, 0x12#8, 0x34#8] := rfl

/-- Reverse a list of bit vectors and flatten the list. -/
def revflat (x : List (BitVec n)) : BitVec (n * x.length) :=
  have h : n * x.reverse.length = n * x.length := by
    simp only [List.length_reverse]
  BitVec.cast h $ BitVec.flatten (List.reverse x)

----------------------------------------------------------------------
-------------------------- Fin and BitVec Lemmas ---------------------

@[ext] protected theorem extensionality_fin (idx1 idx2 : BitVec n)
    (h0 : idx1.toFin = idx2.toFin) :
    idx1 = idx2 := by
    ext
    exact congrArg Fin.val h0

protected theorem extensionality_fin_contrapositive
  {idx1 idx2 : BitVec n} (h0 : ¬idx1 = idx2) :
    idx1.toFin ≠ idx2.toFin :=
  mt (BitVec.extensionality_fin idx1 idx2) h0

theorem bitvec_zero_is_unique (x : BitVec 0) :
  x = 0#0 := by
  apply BitVec.extensionality_fin
  apply Fin.ext
  have h := x.toFin.isLt
  refine Nat.eq_of_le_of_lt_succ ?_ h
  simp only [Nat.pow_zero, Fin.fin_one_eq_zero, Nat.le_refl]

theorem fin_bitvec_add (x y : BitVec n) :
  (x.toFin + y.toFin) = (x + y).toFin := rfl

theorem fin_bitvec_sub (x y : BitVec n) :
  (x.toFin - y.toFin) = (x - y).toFin := rfl

theorem fin_bitvec_or (x y : BitVec n) :
  (x ||| y).toFin = (x.toFin ||| y.toFin) := by
  simp

theorem fin_bitvec_and (x y : BitVec n) :
  (x &&& y).toFin = (x.toFin &&& y.toFin) := by
  simp

theorem fin_bitvec_lt (x y : BitVec n) :
  (x.toFin < y.toFin) ↔ (x < y) := by rfl

theorem fin_bitvec_le (x y : BitVec n) :
  (x.toFin <= y.toFin) ↔ (x <= y) := by rfl

-------------------------- Nat and BitVec Lemmas ---------------------

@[ext] protected theorem extensionality_nat (idx1 idx2 : BitVec n)
    (h0 : idx1.toNat = idx2.toNat) :
    idx1 = idx2 := by
    ext; unfold BitVec.toNat at h0; assumption

protected theorem extensionality_nat_contrapositive
  {idx1 idx2 : BitVec n} (h0 : ¬idx1 = idx2) :
    idx1.toNat ≠ idx2.toNat :=
  mt (BitVec.extensionality_nat idx1 idx2) h0

theorem nat_bitvec_lt (x y : BitVec n) :
  (x.toNat < y.toNat) ↔ (x < y) := by rfl

theorem nat_bitvec_le (x y : BitVec n) :
  (x.toNat <= y.toNat) ↔ (x <= y) := by rfl

theorem nat_bitvec_add (x y : BitVec n) :
  (x + y).toNat = (x.toNat + y.toNat) % 2 ^ n := rfl

theorem nat_bitvec_sub (x y : BitVec n) :
  (x - y).toNat = (x.toNat + (2^n - y.toNat)) % 2^n := by
  have : (x - y).toNat = ((2^n - y.toNat) + x.toNat) % 2^n := rfl
  rw [this, Nat.add_comm]

theorem toNat_ofNat_lt {n w₁ : Nat} (hn : n < 2^w₁) :
    (BitVec.ofNat w₁ n).toNat = n := by
  simp only [toNat_ofNat, Nat.mod_eq_of_lt hn]

---------------------------- Comparison Lemmas -----------------------

theorem ge_of_not_lt (x y : BitVec w₁) (h : ¬ (x < y)) : x ≥ y := by
  simp_all only [BitVec.le_def, BitVec.lt_def]
  omega

protected theorem le_of_eq (x y : BitVec n) (h : x = y) :
  x <= y := by
  simp [←nat_bitvec_le]
  exact Nat.le_of_eq (congrArg BitVec.toNat h)

protected theorem lt_iff_val_lt_val {a b : BitVec n} : a < b ↔ a.toNat < b.toNat :=
  Iff.rfl

protected theorem le_iff_val_le_val {a b : BitVec n} : a ≤ b ↔ a.toNat ≤ b.toNat :=
  Iff.rfl

@[simp]
protected theorem val_bitvec_lt {n : Nat} {a b : BitVec n} : a.toNat < b.toNat ↔ a < b :=
  Iff.rfl

@[simp]
protected theorem val_bitvec_le {n : Nat} {a b : BitVec n} : a.toNat ≤ b.toNat ↔ a ≤ b :=
  Iff.rfl

protected theorem val_nat_le (x y n : Nat)
  (h0 : x <= y) (h1 : x < 2^n) (h2 : y < 2^n) :
  BitVec.ofNat n x <= BitVec.ofNat n y := by
  rw [BitVec.le_iff_val_le_val]
  simp [toNat_ofNat]
  rw [Nat.mod_eq_of_lt h1]
  rw [Nat.mod_eq_of_lt h2]
  trivial

----------------------------- Add/Sub  Lemmas ------------------------

protected theorem zero_le_sub (x y : BitVec n) :
  0#n <= x - y := by
  refine (BitVec.nat_bitvec_le (0#n) (x - y)).mp ?a
  simp only [toNat_ofNat, Nat.zero_mod, toNat_sub, Nat.zero_le]

--------------------- ZeroExtend/Append/Extract  Lemmas ----------------

@[bitvec_rules]
theorem setWidth_zero_width : (setWidth 0 x) = 0#0 := by
  unfold setWidth
  split <;> simp [bitvec_zero_is_unique]

-- During symbolic simulation, we often encounter an `if` in the first argument
-- of `setWidth` (e.g., `read_gpr` reads a specified `width` of the register,
-- which is often computed by checking whether the `instruction.sf` bit is 0 or
-- 1). I've found the rules `setWidth_if_true` and `setWidth_if_false` to be
-- helpful to reduce such occurrences of `setWidth` terms.

@[bitvec_rules]
theorem setWidth_if_true [Decidable p] (x : BitVec n)
  (h_eq : a = (if p then a else b)) :
  (setWidth (if p then a else b) x) = BitVec.cast h_eq (setWidth a x) := by
  simp only [toNat_eq, toNat_setWidth, ← h_eq, toNat_cast]

@[bitvec_rules]
theorem setWidth_if_false [Decidable p] (x : BitVec n)
  (h_eq : b = (if p then a else b)) :
  (setWidth (if p then a else b) x) = BitVec.cast h_eq (setWidth b x) := by
  simp only [toNat_eq, toNat_setWidth, ← h_eq, toNat_cast]

-- TODO: upstream?
@[bitvec_rules]
theorem setWidth_append_right (x : BitVec n) (y : BitVec m) :
    BitVec.setWidth m (x ++ y) = y := by
  apply eq_of_toNat_eq
  simp only [toNat_setWidth, toNat_append]
  rw [← Nat.and_pow_two_sub_one_eq_mod, Nat.and_distrib_right]
  suffices x.toNat <<< m &&& 2 ^ m - 1 = 0
    by simp [this]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.and_pow_two_sub_one_eq_mod, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    ge_iff_le, Nat.zero_testBit, Bool.and_eq_false_imp, decide_eq_true_eq]
  omega

@[bitvec_rules]
protected theorem setWidth_to_lsb_of_append (m n : Nat) (x : BitVec m) (y : BitVec n) :
  setWidth n (x ++ y) = y := by
  simp only [setWidth_append, Nat.le_refl, ↓reduceDIte, setWidth_eq]

theorem extractLsb_eq (x : BitVec n) (h : n = n - 1 + 1) :
  BitVec.extractLsb (n - 1) 0 x = BitVec.cast h x := by
  unfold extractLsb extractLsb'
  ext1
  simp [←h]

@[simp, bitvec_rules]
theorem extractLsb'_eq (x : BitVec n) :
    BitVec.extractLsb' 0 n x = x := by
  unfold extractLsb'
  simp only [Nat.shiftRight_zero, ofNat_toNat, setWidth_eq]

theorem extractLsb'_zero_extractLsb'_of_le (h : len1 ≤ len2) :
  BitVec.extractLsb' 0 len1 (BitVec.extractLsb' start len2 x) =
  BitVec.extractLsb' start len1 x := by
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp only [BitVec.getLsbD_extractLsb', Fin.is_lt,
             decide_True, Nat.zero_add, Bool.true_and,
             Bool.and_iff_right_iff_imp, decide_eq_true_eq]
  omega

theorem extractLsb'_extractLsb'_zero_of_le (h : start + len1 ≤ len2):
  BitVec.extractLsb' start len1 (BitVec.extractLsb' 0 len2 x) =
  BitVec.extractLsb' start len1 x := by
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp only [BitVec.getLsbD_extractLsb', Fin.is_lt,
            decide_True, Nat.zero_add, Bool.true_and,
            Bool.and_iff_right_iff_imp, decide_eq_true_eq]
  omega

-- TODO: upstream
theorem extractLsb'_or (x y : BitVec w₁) (n : Nat) :
    (x ||| y).extractLsb' lo n = (x.extractLsb' lo n ||| y.extractLsb' lo n) := by
  apply BitVec.eq_of_getLsbD_eq
  simp only [getLsbD_extract, getLsbD_or]
  intros i
  simp only [getLsbD_extractLsb', Fin.is_lt, decide_True, getLsbD_or, Bool.true_and]

-- TODO: upstream
protected theorem extractLsb'_ofNat (x n : Nat) (l lo : Nat) :
    extractLsb' lo l (BitVec.ofNat n x) = .ofNat l ((x % 2^n) >>> lo) := by
  apply eq_of_getLsbD_eq
  intro ⟨i, _lt⟩
  simp [BitVec.ofNat]

@[bitvec_rules]
protected theorem extractLsb'_of_setWidth (x : BitVec n) (h : j ≤ i) :
    extractLsb' 0 j (setWidth i x) = setWidth j x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  have q : k < i := by omega
  by_cases h : decide (k ≤ j) <;> simp [q, h]

theorem extractLsb'_append (x : BitVec n) (y : BitVec m) :
    (x ++ y).extractLsb' start len
    = let len' := min len (m - start)
      (x.extractLsb' (start - m) (len - len')
        ++ y.extractLsb' start len'
        ).cast (by omega) := by
  apply eq_of_getLsbD_eq
  intro i
  simp [getLsbD_append]
  by_cases h₁ : m - start ≥ len
  · have len'_eq : min len (m - start) = len := Nat.min_eq_left h₁
    have : start + i.val < m := by omega
    simp [len'_eq, this]
  · have len'_eq : min len (m - start) = m - start :=
      Nat.min_eq_right (by omega)
    simp only [len'_eq]
    by_cases h₂ : start + i.val < m
    · have h₃ : ↑i < m - start := by omega
      simp [h₂, h₃]
    · have h₃ : ¬(↑i < m - start) := by omega
      have h₄ : ↑i - (m - start) < len - (m - start) := by omega
      have h₅ : start - m + (↑i - (m - start)) = start + ↑i - m := by omega
      simp [h₂, h₃, h₄, h₅]

theorem cast_eq_of_heq (x : BitVec n) (y : BitVec m) (h : n = m) :
    HEq x y → x.cast h = y := by
  cases h; simp

theorem cast_heq_iff (x : BitVec n) (y : BitVec m) (h : n = n') :
    HEq (x.cast h) y ↔ HEq x y := by
  cases h; simp

theorem extractLsb'_append_right_of_le (h : start + len ≤ m)
    (x : BitVec n) (y : BitVec m) :
    (x ++ y).extractLsb' start len = y.extractLsb' start len := by
  have len'_eq : min len (m - start) = len := by omega
  simp only [extractLsb'_append]
  apply cast_eq_of_heq
  rw [len'_eq, Nat.sub_self]
  simp only [zero_width_append, heq_eq_eq, cast_heq_iff]

@[bitvec_rules]
theorem extractLsb'_append_right (x : BitVec n) (y : BitVec m) :
    (x ++ y).extractLsb' 0 m = y := by
  rw [extractLsb'_append_right_of_le (by omega), extractLsb'_eq]

@[simp]
theorem extractLsb'_append_left_of_le (h : m ≤ start)
    (x : BitVec n) (y : BitVec m) :
    (x ++ y).extractLsb' start len = x.extractLsb' (start - m) len := by
  have len'_eq : min len (m - start) = m - start := by omega
  simp only [extractLsb'_append]
  apply cast_eq_of_heq
  rw [len'_eq, show m - start = 0 by omega]
  simp only [append_zero_width, heq_eq_eq, cast_heq_iff, Nat.sub_zero]

@[bitvec_rules]
theorem extractLsb'_append_left (x : BitVec n) (y : BitVec m) :
    (x ++ y).extractLsb' m n = x := by
  rw [extractLsb'_append_left_of_le (by omega), Nat.sub_self, extractLsb'_eq]

theorem extractLsb'_extractLsb'_of_le {w : Nat} (start₁ len₁ start₂ len₂)
    (h : start₂ + len₂ ≤ len₁)
    (x : BitVec w) :
    (x.extractLsb' start₁ len₁).extractLsb' start₂ len₂
    = x.extractLsb' (start₁ + start₂) len₂ := by
  apply eq_of_getLsbD_eq
  intro i
  simp only [getLsbD_extractLsb', Fin.is_lt, decide_True, Bool.true_and,
    Bool.and_iff_right_iff_imp, decide_eq_true_eq,
    show start₁ + (start₂ + i.val) = start₁ + start₂ + i.val by ac_rfl]
  omega

@[bitvec_rules, simp]
theorem zero_append {w} (x : BitVec 0) (y : BitVec w) :
    x ++ y = y.cast (by simp) := by
  apply eq_of_getLsbD_eq
  simp only [zero_width_append, getLsbD_cast, implies_true]

@[bitvec_rules]
theorem empty_bitvector_append_left
  (x : BitVec n) (h : 0 + n = n) :
  BitVec.cast h (0#0 ++ x) = x := by
  simp only [cast, zero_width_append, toNat_ofNatLt]
  rfl

-- In case we need ▸ instead of BitVec.cast (and we should really
-- try not to need ▸ because it may break the cast API), applying
-- my_bv_cast_eq_cast and then unfold my_bv_cast should do the trick,
-- like in empty_bitvector_append_left_triangle below.
def my_bv_cast (h : n = m) (x : BitVec n) : BitVec m := h ▸ x

theorem my_bv_cast_eq_cast (x : BitVec n) (h : n = m) :
  my_bv_cast h x = BitVec.cast h x := by
  subst_vars
  simp only [my_bv_cast, BitVec.cast_eq]

theorem empty_bitvector_append_left_triangle
  (x : BitVec n) (h : 0 + n = n) :
  (h ▸ (0#0 ++ x)) = x := by
  have h1 := empty_bitvector_append_left x h
  have h2 := @my_bv_cast_eq_cast
  unfold my_bv_cast at h2
  rw [h2]
  trivial

theorem append_of_extract_general_nat (high low n vn : Nat) (h : vn < 2 ^ n) :
  ((((vn >>> low) % 2 ^ n) % 2 ^ high) <<< low) ||| (vn % 2 ^ low) =
  (vn % 2 ^ (high + low)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]
  by_cases h₀ : (low <= i) ..
  case pos => -- low <= i
    by_cases h₁ : (i < n) ..
    case pos => -- (low <= i) and (i < n)
      simp_all only [decide_True, Bool.true_and]
      have h1 : vn % 2^low < 2^i :=
        calc
         _ < 2^low := by apply Nat.mod_lt; exact Nat.two_pow_pos low
         _ <= 2^i := by apply Nat.pow_le_pow_right; decide; assumption
      simp only [Nat.testBit_lt_two_pow h1, Bool.or_false]
      simp_all only [Nat.testBit_mod_two_pow]
      simp only [Nat.testBit_shiftRight]
      have h3 : i - low < n := by omega
      simp_all [Nat.add_sub_cancel]
      have h4 : (i - low < high) ↔ (i < high + low) := by omega
      simp_all
    case neg => -- (low <= i) and (n <= i)
      simp_all [Nat.not_lt, Nat.testBit_mod_two_pow]
      have h4 : (i - low < high) ↔ (i < high + low) := by omega
      have h5 : ¬(i - low < n - low) := by omega
      have h6 : ¬(i < low) := by omega
      simp [h5, h6]
      rw [Nat.testBit_lt_two_pow]
      · simp [*]
      · apply Nat.lt_of_lt_of_le h
        rwa [Nat.pow_le_pow_iff_right Nat.one_lt_two]
  case neg => -- (i < low)
    simp [h₀]
    simp_all [Nat.testBit_mod_two_pow]
    have h11 : i < high + low := by omega
    simp_all
  done

theorem append_of_extract (n : Nat) (v : BitVec n)
  (high0 : high = n - low) (h : high + low = n) :
  BitVec.cast h (setWidth high (v >>> low) ++ extractLsb' 0 low v) = v := by
  ext
  subst high
  have vlt := v.isLt
  have := append_of_extract_general_nat (n - low) low n (BitVec.toNat v) vlt
  have low_le : low ≤ n := by omega
  simp_all [toNat_setWidth, Nat.sub_add_cancel, low_le]
  rw [Nat.mod_eq_of_lt (b := 2 ^ n)] at this
  · rw [this]
  · rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) vlt
  done

@[bitvec_rules]
theorem append_of_extract_general (v : BitVec n) :
  (setWidth high (v >>> low)) ++ extractLsb' 0 low v =
  extractLsb' 0 (high + low) v := by
  ext
  have := append_of_extract_general_nat high low n (BitVec.toNat v)
  have h_vlt := v.isLt; simp_all only [Nat.sub_zero]
  simp only [h_vlt, forall_prop_of_true] at this
  simp_all [toNat_setWidth, Nat.sub_add_cancel]
  rw [Nat.mod_eq_of_lt (b := 2 ^ n)] at this
  · rw [this]
  · rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h_vlt
  done

theorem leftshift_n_or_mod_2n :
  (x <<< n ||| y) % 2 ^ n = y % 2 ^ n := by
  simp [Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq; intro i
  simp [Nat.testBit_mod_two_pow]
  by_cases h₀ : i < n
  case pos =>
    simp [h₀, Nat.testBit_or]
    rw [@Nat.mul_comm x (2^n)]
    simp [Nat.testBit_mul_pow_two]
    have : ¬(n <= i) := by omega
    simp [this]
  case neg =>
    simp [h₀]

---------------------------- Shift Lemmas ---------------------------

@[bitvec_rules]
protected theorem shift_left_zero_eq (n : Nat) (x : BitVec n) : x <<< 0 = x := by
    refine eq_of_toNat_eq ?_
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [toNat_shiftLeft, Nat.shiftLeft_zero, toNat_mod_cancel]

---------------------------- Negate Lemmas ---------------------------

theorem neg_eq_sub_zero (x : BitVec w₁) : - x = 0 - x := by
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_neg, ofNat_eq_ofNat, toNat_sub, toNat_ofNat, Nat.zero_mod, Nat.add_zero]

----------------------------------------------------------------------

/-! ### Equation Lemmas -/

theorem gt_def {x y : BitVec w} : (x > y) = (x.toNat > y.toNat) := rfl
theorem ge_def {x y : BitVec w} : (x ≥ y) = (x.toNat ≥ y.toNat) := rfl

theorem neq_of_toNat_neq {x y : BitVec w} (hx : x.toNat ≠ y.toNat) : x ≠ y := by
  intros h
  simp [h] at hx

/-! ### (Non) Overflow Rewriting Lemmas

@bollu: To be upstreamed.
-/

private theorem Nat.sub_add_eq_add_sub_of_le_of_le {a b c : Nat} (hab : b ≤ a) (hbc : b ≤ c) :
    a - b + c = a + (c - b) := by
  omega

/- TODO: upstream. -/
theorem toNat_sub_eq_toNat_sub_toNat_of_le {x y : BitVec w} (h : y ≤ x) :
    (x - y).toNat = x.toNat - y.toNat := by
  simp only [toNat_sub]
  rw [BitVec.le_def] at h
  by_cases h' : x.toNat = y.toNat
  · rw [h', Nat.sub_self]
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  · rw [Nat.sub_add_eq_add_sub_of_le_of_le (by omega) (by omega), Nat.add_mod,
      Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]

/- Subtracting bitvectors when there is overflow. -/
theorem toNat_sub_eq_two_pow_sub_add_of_lt
    {a b : BitVec w₁} (hab : a.toNat < b.toNat) : (a - b).toNat = 2^w₁ - b.toNat + a.toNat := by
  simp only [toNat_sub]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem neq_of_lt {x y : BitVec w₁} (h : x < y) : x ≠ y := by
  rintro rfl
  simp [BitVec.lt_def] at h

theorem neq_of_gt {x y : BitVec w₁} (h : x > y) : x ≠ y := by
  rintro rfl
  simp [BitVec.lt_def] at h


/-- adding bitvectors when there is no overflow. -/
theorem toNat_add_eq_toNat_add_toNat {x y : BitVec w} (h : x.toNat + y.toNat < 2^w) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem le_add_self_of_lt (a b : BitVec w₁) (hab : a.toNat + b.toNat < 2^w₁) :
   a ≤ a + b := by
  rw [BitVec.le_def]
  rw [BitVec.toNat_add_eq_toNat_add_toNat (by omega)]
  omega

theorem add_sub_cancel_left {a b : BitVec w₁}
    (hab : a.toNat + b.toNat < 2^w₁) : (a + b) - a = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le]
  · rw [BitVec.toNat_add_eq_toNat_add_toNat (by omega)]
    omega
  · apply BitVec.le_add_self_of_lt
    omega

theorem le_add_iff_sub_le {a b c : BitVec w₁}
   (hac : c ≤ a) (hbc : b.toNat + c.toNat < 2^w₁) :
    (a ≤ b + c) ↔ (a - c ≤ b) := by
  simp_all only [BitVec.le_def]
  rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le (by rw [BitVec.le_def]; omega)]
  rw [BitVec.toNat_add_eq_toNat_add_toNat (by omega)]
  omega

theorem sub_le_sub_iff_right (a b c : BitVec w₁) (hac : c ≤ a)
    (hbc : c ≤ b) : (a - c ≤ b - c) ↔ a ≤ b := by
  simp_all only [BitVec.le_def]
  rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le (by rw [BitVec.le_def]; omega)]
  rw [BitVec.toNat_sub_eq_toNat_sub_toNat_of_le (by rw [BitVec.le_def]; omega)]
  omega

/-! ### Least Significant Byte -/

/--
Definition to extract the `n`th least significant *Byte* from a bitvector.
TODO: this should be named `getLsByte`, or `getLsbByte` (Shilpi prefers this).
-/
def extractLsByte (val : BitVec w₁) (n : Nat) : BitVec 8 :=
  val.extractLsb' (n * 8) 8

theorem extractLsByte_def (val : BitVec w₁) (n : Nat) :
    val.extractLsByte n = val.extractLsb' (n * 8) 8 := rfl

-- TODO: upstream
theorem extractLsb_or (x y : BitVec w₁) (n : Nat) :
    (x ||| y).extractLsb n lo = (x.extractLsb n lo ||| y.extractLsb n lo) := by
  apply BitVec.eq_of_getLsbD_eq
  simp only [getLsbD_extract, getLsbD_or]
  intros i
  by_cases h : (i : Nat) ≤ n - lo
  · simp only [h, decide_True, Bool.true_and]
  · simp only [h, decide_False, Bool.false_and, Bool.or_self]

theorem extractLsByte_zero {w : Nat} : (0#w).extractLsByte i = 0#8 := by
  simp only [extractLsByte, BitVec.extractLsb'_ofNat, Nat.zero_mod, Nat.zero_shiftRight, cast_ofNat]

theorem extractLsByte_ge (h : 8 * a ≥ w₁) (x : BitVec w₁) :
  x.extractLsByte a = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intros i
  simp only [getLsbD_zero, extractLsByte_def,
    getLsbD_cast, getLsbD_extract, Bool.and_eq_false_imp, decide_eq_true_eq]
  simp only [getLsbD_extractLsb', Fin.is_lt, decide_True, Bool.true_and]
  apply BitVec.getLsbD_ge
  omega

@[bitvec_rules]
theorem getLsbD_extractLsByte (val : BitVec w₁) :
    ((BitVec.extractLsByte val n).getLsbD i) =
    (decide (i ≤ 7) && val.getLsbD (n * 8 + i)) := by
  simp only [extractLsByte, getLsbD_cast, getLsbD_extract]
  simp only [getLsbD_extractLsb']
  generalize val.getLsbD (n * 8 + i) = x
  by_cases h : i < 8
  · simp only [show (i : Nat) ≤ 7 by omega, decide_True, Bool.true_and,
    Bool.and_iff_right_iff_imp, decide_eq_true_eq, h]
  · simp only [show ¬(i : Nat) ≤ 7 by omega, decide_False, Bool.false_and,
    Bool.and_eq_false_imp, decide_eq_true_eq, h]

theorem BitVec.getLsbD_eq_false_of_le {w} (x : BitVec w) {i : Nat} (h : w ≤ i) :
    x.getLsbD i = false := by
  exact getLsbD_ge x i h

/--
Two bitvectors of length `n*8` are equal if all their bytes are equal.
This theorem can be strengthened to take `(i : Fin n)`.
-/
theorem eq_of_extractLsByte_eq (x y : BitVec (n * 8))
    (h : ∀ (i : Nat), x.extractLsByte i = y.extractLsByte i) : x = y := by
  apply eq_of_getLsbD_eq
  intros j
  obtain ⟨j, hj⟩ := j
  specialize h (j / 8)
  have hx := x.getLsbD_extractLsByte (n := j / 8) (i := j % 8)
  have hy := y.getLsbD_extractLsByte (n := j / 8) (i := j % 8)
  simp only [show j % 8 ≤ 7 by omega, decide_True, Bool.true_and] at hx hy
  simp only [show j / 8 * 8 + j % 8 = j by omega] at hx hy
  simp only [← hx, ← hy, h]

/-! ### Least Significant Byte range -/

/-- Get `n` least significant bytes of `val`, starting from index `base`.
@bollu: it's not clear if the definition for n=0 is desirable.
-/
def extractLsBytes (val : BitVec w) (base : Nat) (n : Nat) : BitVec (n * 8) :=
  extractLsb' (base * 8) (n * 8) val

@[bitvec_rules]
theorem getLsbD_extractLsBytes (val : BitVec w) (base : Nat) (n : Nat) (i : Nat) :
    (BitVec.extractLsBytes val base n).getLsbD i =
      ((decide (i < n * 8) &&
      val.getLsbD (base * 8 + i))) := by
  rcases n with rfl | n
  · simp only [Nat.reduceMul, Nat.zero_le, getLsbD_ge, Nat.lt_irrefl, decide_False, Nat.zero_mul,
    Nat.add_zero, Bool.false_and]
    simp only [show ¬i < 0 by omega, decide_False, Bool.false_and]
  · simp only [extractLsBytes, getLsbD_cast, getLsbD_extract, Nat.zero_lt_succ, decide_True,
    Bool.true_and]
    by_cases h : i < (n + 1) * 8
    · simp only [getLsbD_extractLsb', h, decide_True, Bool.true_and]
    · simp only [getLsbD_extractLsb', h, decide_False, Bool.false_and]

theorem extractLsByte_extractLsBytes (val : BitVec w) (base : Nat) (n : Nat) (i : Nat) :
    (BitVec.extractLsBytes val base n).extractLsByte i =
    if (i < n) then val.extractLsByte (base + i) else (0#8) := by
  apply BitVec.eq_of_getLsbD_eq
  simp only [getLsbD_extractLsByte, getLsbD_extractLsBytes]
  intros j
  simp only [show (j : Nat) ≤ 7 by omega, decide_True, Bool.true_and]
  by_cases hn : i < n
  · simp only [hn, ↓reduceIte, getLsbD_extractLsByte,
      show (j : Nat) ≤ 7 by omega]
    by_cases h : (i * 8 + (j : Nat) < n * 8)
    · simp only [h, decide_True, Bool.true_and]
      congr 1
      omega
    · simp only [h, decide_False, Bool.false_and, decide_True, Bool.true_and, Bool.false_eq]
      apply BitVec.getLsbD_ge
      omega
  · simp only [hn, ↓reduceIte, getLsbD_zero, Bool.and_eq_false_imp, decide_eq_true_eq]
    omega

/-- Extracting out bytes from the zero bitvector is equal to the zero bitvector. -/
@[bitvec_rules]
theorem extractLsBytes_zero {w : Nat} (base : Nat) :
    (0#w).extractLsBytes base n = 0#(n*8) := by
  apply BitVec.eq_of_getLsbD_eq
  simp only [getLsbD_extractLsBytes, Fin.is_lt, decide_True, getLsbD_zero, Bool.and_false,
    implies_true]

/-- Extracting out all the bytes is equal to the bitvector.
The constraint on the width being `n * 8` is written as
an arbitrary `m` with a hypothesis `hm : m = n * 8`.
This is known in some circles as `fording`. See [1]

[1] https://personal.cis.strath.ac.uk/conor.mcbride/levitation.pdf
-/
@[bitvec_rules]
theorem extractLsBytes_eq_self {n : Nat} {m : Nat}
    (hm : m = n * 8 := by omega)
    (x : BitVec (no_index m)) :
    x.extractLsBytes 0 n = x.cast hm := by
  apply BitVec.eq_of_getLsbD_eq
  intros i
  simp only [getLsbD_extractLsBytes, Nat.zero_mul, Nat.zero_add, Nat.sub_zero]
  simp [show (i : Nat) ≤ n * 8 - 1 by omega]

theorem extractLsBytes_ge (h : a ≥ n) (x : BitVec n) :
  x.extractLsBytes a n = 0#(n*8) := by
  apply BitVec.eq_of_getLsbD_eq
  intros i
  simp only [getLsbD_extractLsBytes, Fin.is_lt, decide_True, Bool.true_and, getLsbD_zero]
  apply BitVec.getLsbD_ge
  omega

/-- TODO: upstream -/
theorem not_slt {w} (a b : BitVec w) : ¬ (a.slt b) ↔ (b.sle a) := by
  simp only [BitVec.slt, BitVec.sle]
  by_cases h : a.toInt < b.toInt
  · simp [h]
    exact Int.not_le.mpr h
  · simp [h]
    exact Int.not_lt.mp h

/-- If subtraction does not overflow,
then `(x - y).toNat` equals `x.toNat - y.toNat` -/
@[deprecated toNat_sub_of_le]
theorem toNat_sub_of_lt' {w} {x y : BitVec w} (h : x.toNat < y.toNat) :
    (y - x).toNat = y.toNat - x.toNat := by
  apply toNat_sub_of_le
  bv_omega

/-- `x.toNat * z.toNat ≤ k` if `z ≤ y` and `x.toNat * y.toNat ≤ k` -/
theorem toNat_mul_toNat_le_of_le_of_le {w} (x y z : BitVec w)
    (hxy : x.toNat * y.toNat ≤ k)
    (hyz : z ≤ y) :
    x.toNat * z.toNat ≤ k := by
  apply Nat.le_trans (m := x.toNat * y.toNat)
  · apply Nat.mul_le_mul_left
    bv_omega
  · exact hxy


/-! ## Length one bitvector lemmas -/

theorem eq_one_iff_neq_zero {a : BitVec 1} : a ≠ 0#1 ↔ a = 1#1 := by bv_omega

theorem eq_zero_iff_neq_one {a : BitVec 1} : a ≠ 1#1 ↔ a = 0#1 := by bv_omega

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

/--
Bitvector pattern component syntax category, originally written by
Leonardo de Moura.
-/
declare_syntax_cat bvpat_comp
syntax num : bvpat_comp
syntax ident ":" num : bvpat_comp

/--
Bitvector pattern syntax category.
Example: [sf:1,0011010000,Rm:5,000000,Rn:5,Rd:5]
-/
declare_syntax_cat bvpat
syntax "[" bvpat_comp,* "]" : bvpat

open Lean

abbrev BVPatComp := TSyntax `bvpat_comp
abbrev BVPat := TSyntax `bvpat

/-- Return the number of bits in a bit-vector component pattern. -/
def BVPatComp.length (c : BVPatComp) : Nat := Id.run do
  match c with
  | `(bvpat_comp| $n:num) =>
    let some str := n.raw.isLit? `num | pure 0
    return str.length
  | `(bvpat_comp| $_:ident : $n:num) =>
    return n.raw.toNat
  | _ =>
    return 0

/--
If the pattern component is a bitvector literal, convert it into a bit-vector term
denoting it.
-/
def BVPatComp.toBVLit? (c : BVPatComp) : MacroM (Option Term) := do
  match c with
  | `(bvpat_comp| $n:num) =>
    let len := c.length
    let some str := n.raw.isLit? `num | Macro.throwErrorAt c "invalid bit-vector literal"
    let bs := str.toList
    let mut val := 0
    for b in bs do
      if b = '1' then
        val := 2*val + 1
      else if b = '0' then
        val := 2*val
      else
        Macro.throwErrorAt c "invalid bit-vector literal, '0'/'1's expected"
    let r ← `(BitVec.ofNat $(quote len) $(quote val))
    return some r
  | _ => return none

/--
If the pattern component is a pattern variable of the form `<id>:<size>` return
`some id`.
-/
def BVPatComp.toBVVar? (c : BVPatComp) : MacroM (Option (TSyntax `ident)) := do
  match c with
  | `(bvpat_comp| $x:ident : $_:num) =>
    return some x
  | _ => return none

def BVPat.getComponents (p : BVPat) : Array BVPatComp :=
  match p with
  | `(bvpat| [$comp,*]) => comp.getElems.reverse
  | _ => #[]

/--
Return the number of bits in a bit-vector pattern.
-/
def BVPat.length (p : BVPat) : Nat := Id.run do
  let mut sz := 0
  for c in p.getComponents do
    sz := sz + c.length
  return sz

/--
Return a term that evaluates to `true` if `var` is an instance of the pattern `pat`.
-/
def genBVPatMatchTest (var : Term) (pat : BVPat) : MacroM Term := do
  let mut shift := 0
  let mut result ← `(true)
  for c in pat.getComponents do
    let len := c.length
    if let some bv ← c.toBVLit? then
      let test ← `(extractLsb' $(quote shift) $(quote len) $var == $bv)
      result ← `($result && $test)
    shift := shift + len
  return result

/--
Given a variable `var` representing a term that matches the pattern `pat`, and a term `rhs`,
return a term of the form
```
let y₁ := var.extract ..
...
let yₙ := var.extract ..
rhs
```
where `yᵢ`s are the pattern variables in `pat`.
-/
def declBVPatVars (var : Term) (pat : BVPat) (rhs : Term) : MacroM Term := do
  let mut result := rhs
  let mut shift  := 0
  for c in pat.getComponents do
    let len := c.length
    if let some y ← c.toBVVar? then
      let rhs ← `(extractLsb' $(quote shift) $(quote len) $var)
      result ← `(let $y := $rhs; $result)
    shift := shift + len
  return result

/--
Define the `match_bv .. with | bvpat => rhs | _ => rhs`.
The last entry is the `else`-case since we currently do not check whether
the patterns are exhaustive or not.
-/
syntax "match_bv " term "with" (atomic("| " bvpat) " => " term)* ("| " "_ " " => " term) : term
macro_rules
  | `(match_bv $discr:term with
      $[ | $ps:bvpat => $rhss:term ]*
         | _ => $rhsElse:term) => do
  let mut result := rhsElse
  let x ← `(discr)
  for p in ps.reverse, rhs in rhss.reverse do
    let test ← genBVPatMatchTest x p
    let rhs ← declBVPatVars x p rhs
    result ← `(if $test then $rhs else $result)
  `(let discr := $discr; $result)

-- def test (x : BitVec 32) : BitVec 16 :=
--   match_bv x with
--   | [sf:1,0011010000,Rm:5,000000,Rn:5,Rd:5] => sf ++ Rm ++ Rn ++ Rd
--   | [sf:1,0000010000,11111000000,Rn:5,Rd:5] => sf ++ Rn ++ Rd ++ Rd
--   | _ => 0#16

-- #print test

-- def test2 (x : BitVec 4) : BitVec 4 :=
--   match_bv x with
--   | [x1:1, x2:1, x3:1, x4:1] => x4 ++ x3 ++ x2 ++ x1
--   | _ => 0#4

-- #print test2

/-- `Quote` instance for `BitVec` -/
instance (w : Nat) : Quote (BitVec w) `term where
  quote x :=
    Syntax.mkCApp ``BitVec.ofNat #[quote w, quote x.toNat]

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

end BitVec

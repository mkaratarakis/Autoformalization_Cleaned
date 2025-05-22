import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example {x y : BitVec w} (h : x.msb = y.msb) :
    x.slt y = x.ult y := by
  -- First, we unfold the definitions of slt and ult.
  unfold slt ult
  -- Next, we simplify the goal using the given hypothesis that the most significant bits are equal.
  simp [h]
  -- We split the goal into two cases based on the value of y.msb.
  split
  · -- Case 1: y.msb = false
    by_cases hy : y.msb
    · -- If y.msb is true, then both x and y are interpreted as negative numbers.
      simp [hy]
      -- The goal simplifies to checking if the natural number representations are equal.
      exact Iff.rfl
    · -- If y.msb is false, then both x and y are interpreted as non-negative numbers.
      simp [hy]
      -- The goal simplifies to checking if the natural number representations are equal.
      exact Iff.rfl
  · -- Case 2: y.msb = true
    by_cases hy : y.msb
    · -- If y.msb is true, then both x and y are interpreted as negative numbers.
      simp [hy]
      -- The goal simplifies to checking if the natural number representations are equal.
      exact Iff.rfl
    · -- If y.msb is false, then both x and y are interpreted as non-negative numbers.
      simp [hy]
      -- The goal simplifies to checking if the natural number representations are equal.
      exact Iff.rfl

/- ACTUAL PROOF OF BitVec.slt_eq_ult_of_msb_eq -/

example {x y : BitVec w} (h : x.msb = y.msb) :
    x.slt y = x.ult y := by
  simp only [BitVec.slt, toInt_eq_msb_cond, BitVec.ult, decide_eq_decide, h]
  cases y.msb <;> simp
import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example {x y : BitVec w} (h : x.msb = y.msb) :
    x.slt y = x.ult y := by
  -- First, we unfold the definitions of slt and ult.
  unfold slt ult
  simp [h]
  split
  · by_cases hy : y.msb
    · simp [hy]
      exact Iff.rfl
    · simp [hy]
      exact Iff.rfl
  · by_cases hy : y.msb
    · simp [hy]
      exact Iff.rfl
    · simp [hy]
      exact Iff.rfl

/- ACTUAL PROOF OF BitVec.slt_eq_ult_of_msb_eq -/

example {x y : BitVec w} (h : x.msb = y.msb) :
    x.slt y = x.ult y := by
  simp only [BitVec.slt, toInt_eq_msb_cond, BitVec.ult, decide_eq_decide, h]
  cases y.msb <;> simp
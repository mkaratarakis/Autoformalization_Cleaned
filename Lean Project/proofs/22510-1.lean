import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example {x y : BitVec w} (h : x.msb = y.msb) :
    x.slt y = x.ult y := by
  unfold slt ult
  simp [h]
  split
  · by_cases ymsb : y.msb
    · simp [ymsb]
      exact Iff.rfl
    · simp [ymsb]
      exact Iff.rfl
  · by_cases ymsb : y.msb
    · simp [ymsb]
      exact Iff.rfl
    · simp [ymsb]
      exact Iff.rfl

/- ACTUAL PROOF OF BitVec.slt_eq_ult_of_msb_eq -/

example {x y : BitVec w} (h : x.msb = y.msb) :
    x.slt y = x.ult y := by
  simp only [BitVec.slt, toInt_eq_msb_cond, BitVec.ult, decide_eq_decide, h]
  cases y.msb <;> simp
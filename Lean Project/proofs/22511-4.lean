import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x y : BitVec w) :
    x.slt y = (x.msb != y.msb).xor (x.ult y) := by
  by_cases h : x.msb = y.msb
  . rw [h]
    simp [Bool.xor_false]
    have h1 : x.slt y = x.ult y := by
      apply BitVec.slt_eq_ult_of_msb_eq
      exact h
    rw [h1]
  . simp [Bool.xor_true]
    have h1 : x.slt y = !x.ult y := by
      apply BitVec.slt_eq_not_ult_of_msb_ne
      exact h
    rw [h1]
    simp only [Bool.xor_eq_iff, Bool.not_not, Bool.not_eq_true_eq_false]
    rfl

/- ACTUAL PROOF OF BitVec.slt_eq_ult -/

example (x y : BitVec w) :
    x.slt y = (x.msb != y.msb).xor (x.ult y) := by
  by_cases h : x.msb = y.msb
  · simp [h, slt_eq_ult_of_msb_eq]
  · have h' : x.msb != y.msb := by simp_all
    simp [slt_eq_not_ult_of_msb_neq h, h']
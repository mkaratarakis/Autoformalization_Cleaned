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
    rw [slt_def, ult_def]
    exact propext (Iff.rfl)
  . rw [slt_def, ult_def]
    simp [Bool.xor_true, propext]
    apply Iff.intro
    . intro h1
      apply False.elim
      exact h (msb_eq_of_slt_eq_false h1)
    . intro h1
      apply False.elim
      exact h (msb_eq_of_ult_eq_true h1)

/- ACTUAL PROOF OF BitVec.slt_eq_ult -/

example (x y : BitVec w) :
    x.slt y = (x.msb != y.msb).xor (x.ult y) := by
  by_cases h : x.msb = y.msb
  · simp [h, slt_eq_ult_of_msb_eq]
  · have h' : x.msb != y.msb := by simp_all
    simp [slt_eq_not_ult_of_msb_neq h, h']
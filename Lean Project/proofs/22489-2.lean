import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x y : BitVec w) : x.ule y = carry w y (~~~x) true := by
  rw [← not_lt]
  rw [← carry_lt]
  rw [not_false_eq_true]

/- ACTUAL PROOF OF BitVec.ule_eq_carry -/

example (x y : BitVec w) : x.ule y = carry w y (~~~x) true := by
  simp [ule_eq_not_ult, ult_eq_not_carry]
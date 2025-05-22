import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x y : BitVec w) :
    x.sle y = !((x.msb == y.msb).xor (carry w y (~~~x) true)) := by
  rw [← BitVec.sle_iff_slt, Bool.not_eq_eq_neg, Bool.not_eq_eq_neg]
  rw [← y.slt]
  rw [y.slt]
  rw [Bool.bxor_eq_eq_neg]
  rw [eq_comm]
  exact Bool.xor_comm ..

/- ACTUAL PROOF OF BitVec.sle_eq_carry -/

example (x y : BitVec w) :
    x.sle y = !((x.msb == y.msb).xor (carry w y (~~~x) true)) := by
  rw [sle_eq_not_slt, slt_eq_not_carry, beq_comm]
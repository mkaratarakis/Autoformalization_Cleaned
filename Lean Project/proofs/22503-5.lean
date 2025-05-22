import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x y : BitVec w) :
    x.sle y = !((x.msb == y.msb).xor (carry w y (~~~x) true)) := by
  rw [← BitVec.slt_iff_sle_not]
  rw [← BitVec.slt_def]
  rw [← BitVec.slt_def]
  rw [← Bool.xor_eq_eq_neg]
  rw [eq_comm]
  rw [Bool.xor_comm]
  apply Bool.xor_comm

/- ACTUAL PROOF OF BitVec.sle_eq_carry -/

example (x y : BitVec w) :
    x.sle y = !((x.msb == y.msb).xor (carry w y (~~~x) true)) := by
  rw [sle_eq_not_slt, slt_eq_not_carry, beq_comm]
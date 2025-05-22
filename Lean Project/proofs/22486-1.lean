import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x y : BitVec w) : x.ult y = !carry w x (~~~y) true := by
  have : x.ult y ↔ x.toNat < y.toNat := by simp [ult, toNat]
  rw [this]
  have : carry w x (~~~y) true = x.toNat + (2^w - 1 - y.toNat) % 2^w + 1 >= 2^w := by
    simp [carry, toNat, bv_add, bv_complement, bv_carry]
    rw [Nat.mod_eq_of_lt]
    apply Nat.lt_of_le_of_lt
    simp [bv_size, bv_to_nat]
  rw [this]
  simp [not_lt, not_not]
  apply omega

/- ACTUAL PROOF OF BitVec.ult_eq_not_carry -/

example (x y : BitVec w) : x.ult y = !carry w x (~~~y) true := by
  simp only [BitVec.ult, carry, toNat_mod_cancel, toNat_not, toNat_true, ge_iff_le, ← decide_not,
    Nat.not_le, decide_eq_decide]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
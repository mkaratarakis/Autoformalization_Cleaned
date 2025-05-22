import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x y : BitVec w) : x.ult y = !carry w x (~~~y) true := by
  have : x.ult y ↔ x.toNat < y.toNat := by simp [ult, toNat]
  rw [this]
  have : carry w x (~~~y) true = bvult x y := by simp [carry, bv_complement, bv_add, bv_carry]
  rw [this]
  simp [not_lt, not_not]
  apply omega

/- ACTUAL PROOF OF BitVec.ult_eq_not_carry -/

example (x y : BitVec w) : x.ult y = !carry w x (~~~y) true := by
  simp only [BitVec.ult, carry, toNat_mod_cancel, toNat_not, toNat_true, ge_iff_le, ← decide_not,
    Nat.not_le, decide_eq_decide]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
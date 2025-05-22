import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example {x y : BitVec w} (h : x &&& y = 0#w) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [← Nat.mod_eq_of_lt (show x.toNat + y.toNat < 2 ^ w from _)]
  simp
  apply carry_bit_of_add_eq_false_iff_and_eq_zero
  exact h

/- ACTUAL PROOF OF BitVec.toNat_add_of_and_eq_zero -/

example {x y : BitVec w} (h : x &&& y = 0#w) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [toNat_add]
  apply Nat.mod_eq_of_lt
  suffices ¬ decide (x.toNat + y.toNat + false.toNat ≥ 2^w) by
    simp only [decide_eq_true_eq] at this
    omega
  rw [← carry_width]
  simp [not_eq_true, carry_of_and_eq_zero h]
import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example {x y : BitVec w} (h : x &&& y = 0#w) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add_mod]
  convert Nat.mod_eq_of_lt (by
    simpa only [decide_eq_true_eq, decide_coe_false, Nat.zero_add (x.toNat + y.toNat)])
  exact bool_iff_of_decide_eq_true (by
    simpa only [decide_coe_false, Nat.zero_add (x.toNat + y.toNat)]
    exact carry_bit_of_add_eq_true_iff_toNat_ge_pow_two_width (by
      simpa only [Bool.decide_coe_bool_false]
      exact Eq.symm h)

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
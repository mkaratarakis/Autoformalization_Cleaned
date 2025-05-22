import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example {x y : BitVec w} (h : x &&& y = 0#w) :
    (x + y).toNat = x.toNat + y.toNat := by
  have h1 : (x.toNat + y.toNat) % (2 ^ w) = x.toNat + y.toNat := by
    apply Nat.mod_eq_of_lt
    suffices : (x.toNat + y.toNat + false.toNat) < 2^w
    exact this
    rw [Nat.lt_iff_add_one_le]
    rw [Nat.le_iff_exists_add]
    use 2^w
    rw [Nat.add_comm]
    rw [Nat.add_assoc]
    rw [Nat.add_comm (x.toNat + y.toNat) 1]
    rw [Nat.add_comm (x.toNat + y.toNat + 1)]
    rw [Nat.add_comm (2^w)]
    rw [Nat.add_assoc]
    rw [Nat.add_comm (x.toNat + y.toNat + 1)]
    rw [Nat.add_assoc]
    rw [Nat.add_comm (2^w)]
    apply carry_bit_of_add_eq_false_iff_and_eq_zero
    exact h
  rw [h1]
  rfl

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
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Algebra.Order.Group.Lattice


open Function
variable {α β : Type*}
variable [Lattice α] [Group α]
variable [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]

example 
    {a : α} (ha : 1 ≤ a ^ 2) : 1 ≤ a := by
  rw [← one_mul (a ⊓ 1), ← one_mul (a ⊓ 1), ← mul_assoc, ← mul_assoc]
  apply le_of_eq
  calc
    (a ⊓ 1) * (a ⊓ 1) = (1 * a) ⊓ (1 * 1) * (a ⊓ 1) := by rw [mul_inf, one_mul, mul_one]
    _ = a ⊓ (a ^ 2 ⊓ 1) := by rw [mul_inf, mul_inf, pow_two]
    _ = a ⊓ 1 := by rw [inf_of_le_right ha]

/- ACTUAL PROOF OF pow_two_semiclosed -/

example 
    {a : α} (ha : 1 ≤ a ^ 2) : 1 ≤ a := by
  suffices this : (a ⊓ 1) * (a ⊓ 1) = a ⊓ 1 by
    rwa [← inf_eq_right, ← mul_right_eq_self]
  rw [mul_inf, inf_mul, ← pow_two, mul_one, one_mul, inf_assoc, inf_left_idem, inf_comm,
    inf_assoc, inf_of_le_left ha]
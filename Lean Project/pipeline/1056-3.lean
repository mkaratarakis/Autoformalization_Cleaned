import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Algebra.Order.Group.Lattice


open Function
variable {α β : Type*}
variable [Lattice α] [Group α]
variable [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]

example 
    {a : α} (ha : 1 ≤ a ^ 2) : 1 ≤ a := by
  rw [← one_mul (a ⊓ 1)]
  calc
    (a ⊓ 1) * (a ⊓ 1) = (a ⊓ 1) * a ⊓ (a ⊓ 1) * 1 := by rw [mul_one]
    ... = (a ⊓ 1) * a ⊓ (a ⊓ 1) := by rw [inf_mul]
    ... = a * a ⊓ a ⊓ (a ⊓ 1) := by
      rw [mul_inf, ← mul_assoc, inf_assoc, inf_comm (a ⊓ 1) a, inf_left_idem]
    ... = a ^ 2 ⊓ (a ⊓ 1) := by rw [pow_two]
    ... = 1 ⊓ (a ⊓ 1) := by rw [ha, inf_comm (a ⊓ 1) 1, inf_left_comm]
    ... = a ⊓ 1 := by rw [inf_idem]

  exact le_of_eq this

/- ACTUAL PROOF OF pow_two_semiclosed -/

example 
    {a : α} (ha : 1 ≤ a ^ 2) : 1 ≤ a := by
  suffices this : (a ⊓ 1) * (a ⊓ 1) = a ⊓ 1 by
    rwa [← inf_eq_right, ← mul_right_eq_self]
  rw [mul_inf, inf_mul, ← pow_two, mul_one, one_mul, inf_assoc, inf_left_idem, inf_comm,
    inf_assoc, inf_of_le_left ha]
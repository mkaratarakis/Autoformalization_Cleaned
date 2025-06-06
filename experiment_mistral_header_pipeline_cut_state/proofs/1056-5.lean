import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Algebra.Order.Group.Lattice


open Function
variable {α β : Type*}
variable [Lattice α] [Group α]
variable [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]

example 
    {a : α} (ha : 1 ≤ a ^ 2) : 1 ≤ a := by
  have h : (a ⊓ 1) * (a ⊓ 1) = a ⊓ 1 := by
    calc
      (a ⊓ 1) * (a ⊓ 1)
        = (a * a ⊓ 1) ⊓ (a * 1 ⊓ 1) := by rw [mul_inf, mul_inf, one_mul]
      ... = (a ^ 2 ⊓ 1) ⊓ (a ⊓ 1) := by rw [sq, one_mul]
      ... = (1 ⊓ a ^ 2) ⊓ (a ⊓ 1) := by rw [ha, inf_comm]
      ... = a ⊓ 1 := by rw [inf_idem, inf_comm]
  have : a ⊓ 1 = 1 := by
    apply le_antisymm
    · exact inf_le_right
    · rw [h]
      apply le_inf (le_of_mul_le_one_right ha) le_rfl
  exact this

/- ACTUAL PROOF OF pow_two_semiclosed -/

example 
    {a : α} (ha : 1 ≤ a ^ 2) : 1 ≤ a := by
  suffices this : (a ⊓ 1) * (a ⊓ 1) = a ⊓ 1 by
    rwa [← inf_eq_right, ← mul_right_eq_self]
  rw [mul_inf, inf_mul, ← pow_two, mul_one, one_mul, inf_assoc, inf_left_idem, inf_comm,
    inf_assoc, inf_of_le_left ha]
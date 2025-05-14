import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.GroupWithZero.Divisibility

open IsPrimal
variable {α : Type*}
variable [SemigroupWithZero α] {a : α}
variable [CommMonoidWithZero α]
variable {x y : α}
variable [MonoidWithZero α]

example {α} [CancelCommMonoidWithZero α] {m n : α}
    (hm : IsPrimal m) (hn : IsPrimal n) : IsPrimal (m * n) := by
  by_cases hm0 : m = 0
  · exact isPrimal_zero

  · intro b c hdiv
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := hm (hm0 ∘ MulZero.eq_zero_of_left).symm hdiv
    have := hn (ha₁.trans (Dvd.mul_right _ _)).symm (ha₂.trans (Dvd.mul_right _ _))
    obtain ⟨a₁', a₂', ha₁', ha₂', rfl⟩ := this
    exact ⟨a₁ * a₁', a₂ * a₂', ha₁.trans (Dvd.mul_left _ _), ha₂.trans (Dvd.mul_left _ _), mul_assoc _ _ _⟩

/- ACTUAL PROOF OF IsPrimal.mul -/

example {α} [CancelCommMonoidWithZero α] {m n : α}
    (hm : IsPrimal m) (hn : IsPrimal n) : IsPrimal (m * n) := by
  obtain rfl | h0 := eq_or_ne m 0; · rwa [zero_mul]
  intro b c h
  obtain ⟨a₁, a₂, ⟨b, rfl⟩, ⟨c, rfl⟩, rfl⟩ := hm (dvd_of_mul_right_dvd h)
  rw [mul_mul_mul_comm, mul_dvd_mul_iff_left h0] at h
  obtain ⟨a₁', a₂', h₁, h₂, rfl⟩ := hn h
  exact ⟨a₁ * a₁', a₂ * a₂', mul_dvd_mul_left _ h₁, mul_dvd_mul_left _ h₂, mul_mul_mul_comm _ _ _ _⟩
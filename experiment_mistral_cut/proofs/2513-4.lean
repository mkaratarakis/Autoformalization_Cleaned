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
  · simp [hm0]

  · intro b c h
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := hm (Dvd.trans (Dvd.intro m rfl) h)
    rw [← ha₂] at h
    obtain ⟨a₃, a₄, ha₃, ha₄, rfl⟩ := hn (Dvd.trans (Dvd.intro n (mul_right_inj' ha₂)) h)
    refine' ⟨a₁ * a₃, a₂ * a₄, _, _, by rw [mul_assoc, mul_assoc, ←mul_assoc (a₁ * a₃), ←mul_assoc a₂, ←mul_assoc a₄, mul_left_comm a₁, ←mul_assoc, mul_comm a₂, mul_left_comm a₃]⟩
    · exact Dvd.trans ha₁ (Dvd.intro _ (mul_assoc _ _ _).symm)
    · exact Dvd.trans ha₄ (Dvd.intro _ (mul_assoc _ _ _).symm)

/- ACTUAL PROOF OF IsPrimal.mul -/

example {α} [CancelCommMonoidWithZero α] {m n : α}
    (hm : IsPrimal m) (hn : IsPrimal n) : IsPrimal (m * n) := by
  obtain rfl | h0 := eq_or_ne m 0; · rwa [zero_mul]
  intro b c h
  obtain ⟨a₁, a₂, ⟨b, rfl⟩, ⟨c, rfl⟩, rfl⟩ := hm (dvd_of_mul_right_dvd h)
  rw [mul_mul_mul_comm, mul_dvd_mul_iff_left h0] at h
  obtain ⟨a₁', a₂', h₁, h₂, rfl⟩ := hn h
  exact ⟨a₁ * a₁', a₂ * a₂', mul_dvd_mul_left _ h₁, mul_dvd_mul_left _ h₂, mul_mul_mul_comm _ _ _ _⟩
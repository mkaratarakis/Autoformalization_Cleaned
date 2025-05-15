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
  intros b c h
  by_cases hm0 : m = 0
  · simp only [hm0, zero_mul]
    exact ⟨0, 0, dvd_zero _, dvd_zero _, by rw [zero_mul]⟩

  · have hn0 : n ≠ 0 := by
      intro hn0
      apply hm0
      rw [hn0, zero_mul] at h
      exact (zero_dvd_iff α).mp h

    obtain ⟨k, hk⟩ := h
    have hmn : m * n ∣ b * c := ⟨k, hk⟩
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := hm hmn
    obtain ⟨b₁, b₂, hb₁, hb₂, hmn⟩ := hn (mul_ne_zero hm0 hn0).symm ▸ hmn
    use a₁ * b₁, a₂ * b₂
    rw [mul_assoc, ← hmn, mul_assoc, ← mul_assoc a₂, ← hmn, mul_assoc, mul_assoc]

    constructor
    · exact mul_dvd_mul_left _ (ha₁.trans (dvd_mul_right _ _))

    · exact mul_dvd_mul_left _ (ha₂.trans (dvd_mul_right _ _))

    · exact mul_dvd_mul_left _ (hb₁.trans (dvd_mul_left _ _))

    · exact mul_dvd_mul_left _ (hb₂.trans (dvd_mul_left _ _))

/- ACTUAL PROOF OF IsPrimal.mul -/

example {α} [CancelCommMonoidWithZero α] {m n : α}
    (hm : IsPrimal m) (hn : IsPrimal n) : IsPrimal (m * n) := by
  obtain rfl | h0 := eq_or_ne m 0; · rwa [zero_mul]
  intro b c h
  obtain ⟨a₁, a₂, ⟨b, rfl⟩, ⟨c, rfl⟩, rfl⟩ := hm (dvd_of_mul_right_dvd h)
  rw [mul_mul_mul_comm, mul_dvd_mul_iff_left h0] at h
  obtain ⟨a₁', a₂', h₁, h₂, rfl⟩ := hn h
  exact ⟨a₁ * a₁', a₂ * a₂', mul_dvd_mul_left _ h₁, mul_dvd_mul_left _ h₂, mul_mul_mul_comm _ _ _ _⟩
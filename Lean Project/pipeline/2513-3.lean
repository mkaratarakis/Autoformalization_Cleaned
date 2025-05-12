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
  by_cases h : m = 0
  · simp [h]
  · intros b c hbc
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := hm (Dvd.intro (m * n) hbc)
    obtain ⟨a₁', a₂', ha₁', ha₂', rfl⟩ := hn (Dvd.intro a₂ ha₂)
    exact ⟨a₁ * a₁', a₂ * a₂', Dvd.intro (a₁ * a₁') (Dvd.trans ha₁ (Dvd.intro a₁' (dvd_refl a₁'))), Dvd.intro (a₂ * a₂') (Dvd.trans ha₂ (Dvd.intro a₂' (dvd_refl a₂'))), by
      rw [mul_assoc, mul_assoc, mul_assoc, mul_comm n a₂, ←mul_assoc, ←mul_assoc, ←mul_assoc, mul_comm a₁' a₁, ←mul_assoc, mul_comm a₁ a₁', ←mul_assoc, mul_comm a₂ a₂', ←mul_assoc]⟩

/- ACTUAL PROOF OF IsPrimal.mul -/

example {α} [CancelCommMonoidWithZero α] {m n : α}
    (hm : IsPrimal m) (hn : IsPrimal n) : IsPrimal (m * n) := by
  obtain rfl | h0 := eq_or_ne m 0; · rwa [zero_mul]
  intro b c h
  obtain ⟨a₁, a₂, ⟨b, rfl⟩, ⟨c, rfl⟩, rfl⟩ := hm (dvd_of_mul_right_dvd h)
  rw [mul_mul_mul_comm, mul_dvd_mul_iff_left h0] at h
  obtain ⟨a₁', a₂', h₁, h₂, rfl⟩ := hn h
  exact ⟨a₁ * a₁', a₂ * a₂', mul_dvd_mul_left _ h₁, mul_dvd_mul_left _ h₂, mul_mul_mul_comm _ _ _ _⟩
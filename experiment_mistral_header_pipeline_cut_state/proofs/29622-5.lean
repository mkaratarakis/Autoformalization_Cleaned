import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

open ZMod
open Nat
variable {p : ℕ} [Fact p.Prime]
open ZMod

example (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  have hp_odd : 2 < p := by
    apply lt_of_ne_of_le
    · intro h
      rw [h] at hp
      exact hp rfl
    · apply Nat.Prime.two_le (Fact.out p.Prime)
  rw [FiniteField.isSquare_neg_two_iff]
  rw [not_and_or]
  rw [not_not]
  rw [Ne.def]
  rw [Ne.def]
  push_neg
  rw [or_and_distrib_right]
  rw [and_self_iff]
  rw [or_false_iff]
  rw [not_or]
  rw [not_not]
  rw [Ne.def]
  rw [Ne.def]
  push_neg
  rw [and_or_distrib_right]
  rw [or_self_iff]
  rw [false_or_iff]
  exact Iff.rfl

/- ACTUAL PROOF OF ZMod.exists_sq_eq_neg_two_iff -/

example (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  rw [FiniteField.isSquare_neg_two_iff, card p]
  have h₁ := Prime.mod_two_eq_one_iff_ne_two.mpr hp
  rw [← mod_mod_of_dvd p (by decide : 2 ∣ 8)] at h₁
  have h₂ := mod_lt p (by norm_num : 0 < 8)
  revert h₂ h₁
  generalize p % 8 = m; clear! p
  intros; interval_cases m <;> simp_all
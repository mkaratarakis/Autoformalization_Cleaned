import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

open ZMod
open Nat
variable {p : ℕ} [Fact p.Prime]
open ZMod

example (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  rw [← FiniteField.isSquare_neg_two_iff]
  simp only [card p]
  rw [← not_iff_not, Ne.def, Nat.not_and_or]
  push_neg
  rw [← not_or_distrib]
  push_neg
  rw [← Nat.Prime.ne_two_iff_even]
  · simp only [Nat.even_iff, not_or, Nat.Prime.mod_two_ne_zero hp]
  · rw [← Nat.odd_iff_not_even]
    simp only [Nat.odd_iff_mod_two_eq_one]
    exact Nat.Prime.mod_two_ne_zero hp
  · exact Nat.Prime.mod_two_ne_zero hp
  · exact Nat.Prime.mod_two_ne_zero hp
  · exact Nat.Prime.mod_two_ne_zero hp
  · exact Nat.Prime.mod_two_ne_zero hp

/- ACTUAL PROOF OF ZMod.exists_sq_eq_neg_two_iff -/

example (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  rw [FiniteField.isSquare_neg_two_iff, card p]
  have h₁ := Prime.mod_two_eq_one_iff_ne_two.mpr hp
  rw [← mod_mod_of_dvd p (by decide : 2 ∣ 8)] at h₁
  have h₂ := mod_lt p (by norm_num : 0 < 8)
  revert h₂ h₁
  generalize p % 8 = m; clear! p
  intros; interval_cases m <;> simp_all
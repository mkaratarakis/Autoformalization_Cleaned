import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

open ZMod
open Nat
variable {p : ℕ} [Fact p.Prime]
open ZMod

example (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  have h_p_odd : p % 2 = 1 := by
    exact Nat.Prime.mod_two_eq_one_of_ne_two hp

  have h_p_mod_8_mod_2 : p % 8 % 2 = 1 := by
    rw [h_p_odd]

  have h_p_mod_8_lt_8 : p % 8 < 8 := by
    exact Nat.mod_lt p 8

  have h_p_mod_8_ne_5_and_ne_7 : p % 8 ≠ 5 ∧ p % 8 ≠ 7 := by
    rw [h_p_mod_8_mod_2]
    simp

  rw [← FiniteField.isSquare_neg_two_iff]
  rw [h_p_mod_8_ne_5_and_ne_7]
  simp [h_p_mod_8_lt_8]
  tauto

/- ACTUAL PROOF OF ZMod.exists_sq_eq_neg_two_iff -/

example (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  rw [FiniteField.isSquare_neg_two_iff, card p]
  have h₁ := Prime.mod_two_eq_one_iff_ne_two.mpr hp
  rw [← mod_mod_of_dvd p (by decide : 2 ∣ 8)] at h₁
  have h₂ := mod_lt p (by norm_num : 0 < 8)
  revert h₂ h₁
  generalize p % 8 = m; clear! p
  intros; interval_cases m <;> simp_all
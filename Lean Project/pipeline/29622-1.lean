import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

open ZMod
open Nat
variable {p : ℕ} [Fact p.Prime]
open ZMod

example (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  have h_zmod_p_ne_zero : (p : ZMod p) ≠ 0 := by
    intro hp_zero
    apply hp
    rw [hp_zero]

  have h_2_ne_zero : (2 : ZMod p) ≠ 0 := by
    intro h_2_zero
    apply hp
    rw [h_2_zero]

  have h_neg_2_ne_zero : (-2 : ZMod p) ≠ 0 := by
    intro h_neg_2_zero
    apply h_2_ne_zero
    rw [h_neg_2_zero]

  have h_p_odd : p % 2 = 1 := by
    have h_p_ne_2 : p ≠ 2 := hp
    have h_p_prime : Fact p.Prime := Fact.out p.Prime
    have h_p_odd : 2 ∤ p := by
      intro h_2_dvd_p
      apply h_p_ne_2
      rw [h_2_dvd_p]
    rw [Nat.Prime.mod_two_eq_one_of_ne_two h_p_prime h_p_ne_2]

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
  omega

/- ACTUAL PROOF OF ZMod.exists_sq_eq_neg_two_iff -/

example (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  rw [FiniteField.isSquare_neg_two_iff, card p]
  have h₁ := Prime.mod_two_eq_one_iff_ne_two.mpr hp
  rw [← mod_mod_of_dvd p (by decide : 2 ∣ 8)] at h₁
  have h₂ := mod_lt p (by norm_num : 0 < 8)
  revert h₂ h₁
  generalize p % 8 = m; clear! p
  intros; interval_cases m <;> simp_all
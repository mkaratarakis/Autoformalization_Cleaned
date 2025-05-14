import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

open ZMod
open Nat
variable {p : ℕ} [Fact p.Prime]
open ZMod

example (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  rw [isSquare_iff_legendre_eq_one, legendreSym_neg, legendreSym_two]
  split_ifs with hp2
  · exfalso; exact hp hp2
  · rw [ZMod.nat_cast_one']
    have : (p : ZMod 8) = ((p : ZMod p) : ZMod 8) := rfl
    rw [this, ZMod.nat_cast_one', ZMod.nat_cast_bit0, ZMod.nat_cast_one']
    norm_num

/- ACTUAL PROOF OF ZMod.exists_sq_eq_neg_two_iff -/

example (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  rw [FiniteField.isSquare_neg_two_iff, card p]
  have h₁ := Prime.mod_two_eq_one_iff_ne_two.mpr hp
  rw [← mod_mod_of_dvd p (by decide : 2 ∣ 8)] at h₁
  have h₂ := mod_lt p (by norm_num : 0 < 8)
  revert h₂ h₁
  generalize p % 8 = m; clear! p
  intros; interval_cases m <;> simp_all
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open jacobiSym
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example {a b : ℕ} (ha : a % 4 = 1) (hb : Odd b) :
    J(a | b) = J(b | a) := by
  have hb_ne_zero : b ≠ 0 := by simpa using hb
  rw [jacobiSym.quadratic_reciprocity]
  have : (-1 : ℤ) ^ ((a - 1) / 2 * (b - 1) / 2) = 1 := by
    rw [pow_eq_one_iff]
    apply And.intro
    · have : 2 ∣ (a - 1) := by
      rw [← ha]
      exact dvd_sub (dvd_mul_right _ _) (dvd_refl _)
    · exact ⟨Nat.mod_two_eq_one_iff.mpr hb, rfl⟩
  rw [this, one_mul]

/- ACTUAL PROOF OF jacobiSym.quadratic_reciprocity_one_mod_four -/

example {a b : ℕ} (ha : a % 4 = 1) (hb : Odd b) :
    J(a | b) = J(b | a) := by
  rw [quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb, pow_mul,
    neg_one_pow_div_two_of_one_mod_four ha, one_pow, one_mul]
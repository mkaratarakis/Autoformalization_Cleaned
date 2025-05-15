import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open jacobiSym
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example {a b : ℕ} (ha : a % 4 = 1) (hb : Odd b) :
    J(a | b) = J(b | a) := by
  have hb_ne_zero : b ≠ 0 := by simpa using hb
  rw [← jacobiSym.quadratic_reciprocity (Nat.Prime.mod_four_eq_one_iff.mpr ha) hb]
  have : (-1 : ℤ) ^ (a / 2 * b / 2) = 1 := by
    rw [Nat.mod_eq_of_lt (Nat.div_lt_of_pos_of_le ha.le (Nat.succ_pos 3))]
    simp [ZMod.nat_cast_eq_zmod_cast]
    exact pow_eq_one_of_even (Nat.mul_div_right (Nat.div_dvd_of_dvd (dvd_mul_right _ _) ha))
  rw [this, one_mul]
  exact jacobiSym.quadratic_reciprocity_one_mod_four (Nat.Prime.mod_four_eq_one_iff.mpr ha) hb

/- ACTUAL PROOF OF jacobiSym.quadratic_reciprocity_one_mod_four -/

example {a b : ℕ} (ha : a % 4 = 1) (hb : Odd b) :
    J(a | b) = J(b | a) := by
  rw [quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb, pow_mul,
    neg_one_pow_div_two_of_one_mod_four ha, one_pow, one_mul]
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open jacobiSym
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  cases' h : a with a_neg
  · -- Case 1: a = natAbs a
    apply jacobiSym.mod_right
  · -- Case 2: a = -natAbs a
    have h_odd : Odd (b % (4 * a_neg)) := by
      apply Nat.odd_mod
      · exact hb
      · exact Nat.mul_ne_zero 4 a_neg.ne_zero
    calc
      J(a | b) = J(-a_neg | b) := rfl
      _ = χ₄ b * J(a_neg | b) := jacobiSym.neg_right _ _ hb
      _ = χ₄ b * J(a_neg | b % (4 * a_neg)) := (jacobiSym.mod_right a_neg b (4 * a_neg)).symm
      _ = χ₄ (b % (4 * a_neg)) * J(a_neg | b % (4 * a_neg)) := by congr; exact char_four_mod_eq b (4 * a_neg)
      _ = J(-a_neg | b % (4 * a_neg)) := (jacobiSym.neg_right _ _ h_odd).symm
      _ = J(a | b % (4 * a.natAbs)) := rfl

/- ACTUAL PROOF OF jacobiSym.mod_right -/

example (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  cases' Int.natAbs_eq a with ha ha <;> nth_rw 2 [ha] <;> nth_rw 1 [ha]
  · exact mod_right' a.natAbs hb
  · have hb' : Odd (b % (4 * a.natAbs)) := hb.mod_even (Even.mul_right (by decide) _)
    rw [jacobiSym.neg _ hb, jacobiSym.neg _ hb', mod_right' _ hb, χ₄_nat_mod_four,
      χ₄_nat_mod_four (b % (4 * _)), mod_mod_of_dvd b (dvd_mul_right 4 _)]
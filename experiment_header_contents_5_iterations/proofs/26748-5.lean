import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open jacobiSym
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  by_cases h : 0 ≤ a
  · -- Case 1: a = natAbs a
    exact jacobiSym.mod_right _ _ _
  · -- Case 2: a = -natAbs a
    have h_odd : Odd (b % (4 * a.natAbs)) := by
      apply Nat.odd_of_mod_of_even
      · exact hb
      · exact mul_ne_zero four_ne_zero (natAbs_ne_zero_of_ne_zero (Int.ne_of_lt (Int.neg_pos_of_neg h)).symm)
    calc
      J(a | b) = J(-a.natAbs | b) := by rw [Int.neg_eq_natAbs h]
      _ = χ₄ b * J(a.natAbs | b) := jacobiSym.neg_right _ _ hb
      _ = χ₄ b * J(a.natAbs | b % (4 * a.natAbs)) := (jacobiSym.mod_right a.natAbs _ _).symm
      _ = χ₄ (b % (4 * a.natAbs)) * J(a.natAbs | b % (4 * a.natAbs)) := by congr; exact char_four_mod_eq b (4 * a.natAbs)
      _ = J(-a.natAbs | b % (4 * a.natAbs)) := (jacobiSym.neg_right _ _ h_odd).symm
      _ = J(a | b % (4 * a.natAbs)) := by rw [Int.neg_eq_natAbs h]

/- ACTUAL PROOF OF jacobiSym.mod_right -/

example (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  cases' Int.natAbs_eq a with ha ha <;> nth_rw 2 [ha] <;> nth_rw 1 [ha]
  · exact mod_right' a.natAbs hb
  · have hb' : Odd (b % (4 * a.natAbs)) := hb.mod_even (Even.mul_right (by decide) _)
    rw [jacobiSym.neg _ hb, jacobiSym.neg _ hb', mod_right' _ hb, χ₄_nat_mod_four,
      χ₄_nat_mod_four (b % (4 * _)), mod_mod_of_dvd b (dvd_mul_right 4 _)]
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open jacobiSym
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  by_cases ha : a = a.natAbs
  · exact jacobiSym.mod_right a.natAbs b hb
  · push_neg at ha
    rw [Int.natAbs_eq_of_neg ha]
    have h_odd : Odd (b % (4 * a.natAbs)) := by
      rw [Nat.odd_iff]
      exact Nat.mod_two_eq_one_iff.mpr (hb.mod_cast.symm.mod_cast)
    rw [jacobiSym.neg_right, jacobiSym.neg_right, ← Int.natAbs_eq_of_neg ha,
        ← Int.natAbs_eq_of_neg ha, jacobiSym.mod_right a.natAbs b hb,
        jacobiSym.mod_right a.natAbs (b % (4 * a.natAbs)) h_odd, χ₄.mod_four,
        Nat.mod_mod_of_dvd _ (dvd_mul_right _ _), χ₄.mod_four,
        Nat.mod_mod_of_dvd _ (dvd_mul_right _ _)]
    rfl

/- ACTUAL PROOF OF jacobiSym.mod_right -/

example (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  cases' Int.natAbs_eq a with ha ha <;> nth_rw 2 [ha] <;> nth_rw 1 [ha]
  · exact mod_right' a.natAbs hb
  · have hb' : Odd (b % (4 * a.natAbs)) := hb.mod_even (Even.mul_right (by decide) _)
    rw [jacobiSym.neg _ hb, jacobiSym.neg _ hb', mod_right' _ hb, χ₄_nat_mod_four,
      χ₄_nat_mod_four (b % (4 * _)), mod_mod_of_dvd b (dvd_mul_right 4 _)]
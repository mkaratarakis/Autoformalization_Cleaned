import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open jacobiSym
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  cases h : a
  · rw [jacobiSym.mod_right]
    exact hb
  · rw [Int.natAbs_neg]
    have hodd : Odd (b % (4 * a.natAbs)) := by
      rw [Nat.mod_mod_of_dvd (dvd_mul_right _ _)]
      exact hb
    rw [jacobiSym.neg_right]
    rw [jacobiSym.mod_right]
    rw [χ₄_eq_χ₄_mod a.natAbs (Nat.mod_mod_of_dvd (dvd_mul_right _ _))]
    rw [Nat.mod_mod_of_dvd (dvd_mul_right _ _)]
    congr
    exact χ₄_eq_χ₄_mod a.natAbs (Nat.mod_mod_of_dvd (dvd_mul_right _ _))

/- ACTUAL PROOF OF jacobiSym.mod_right -/

example (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  cases' Int.natAbs_eq a with ha ha <;> nth_rw 2 [ha] <;> nth_rw 1 [ha]
  · exact mod_right' a.natAbs hb
  · have hb' : Odd (b % (4 * a.natAbs)) := hb.mod_even (Even.mul_right (by decide) _)
    rw [jacobiSym.neg _ hb, jacobiSym.neg _ hb', mod_right' _ hb, χ₄_nat_mod_four,
      χ₄_nat_mod_four (b % (4 * _)), mod_mod_of_dvd b (dvd_mul_right 4 _)]
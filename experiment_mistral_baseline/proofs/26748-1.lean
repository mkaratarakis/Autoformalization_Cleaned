import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open jacobiSym
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  cases h : a with
  | ofNat n =>
    rw [h]
    exact jacobi_mod_of_pos n hb (by norm_num : 0 < 4 * n)
  | negSucc n =>
    have hb' : Odd (b % (4 * n.succ)) := by
      exact Nat.odd_of_mod_by_even hb (by norm_num : Odd (4 * n.succ))
    rw [jacobi_neg_of_odd]
    rw [jacobi_neg_of_odd, jacobi_mod_of_pos n hb (by norm_num : 0 < 4 * n.succ)]
    rw [← jacobi_neg_of_odd, ← jacobi_neg_of_odd]
    rw [chi_four_eq_chi_four_mod_four]
    rw [← ZMod.nat_mod_mod, ZMod.nat_mod_mod]
    rw [Nat.mod_mod_of_dvd (by exact dvd_mul_right (4 : ℕ) n.succ)]

/- ACTUAL PROOF OF jacobiSym.mod_right -/

example (a : ℤ) {b : ℕ} (hb : Odd b) : J(a | b) = J(a | b % (4 * a.natAbs)) := by
  cases' Int.natAbs_eq a with ha ha <;> nth_rw 2 [ha] <;> nth_rw 1 [ha]
  · exact mod_right' a.natAbs hb
  · have hb' : Odd (b % (4 * a.natAbs)) := hb.mod_even (Even.mul_right (by decide) _)
    rw [jacobiSym.neg _ hb, jacobiSym.neg _ hb', mod_right' _ hb, χ₄_nat_mod_four,
      χ₄_nat_mod_four (b % (4 * _)), mod_mod_of_dvd b (dvd_mul_right 4 _)]
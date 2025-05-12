import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open jacobiSym
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example {a b : ℕ} (ha : a % 4 = 1) (hb : Odd b) :
    J(a | b) = J(b | a) := by
  have h_odd_a : Odd a := by
    rw [ha]
    exact Odd.intro 1 (by decide)
  have h_quad_recip : J(a | b) = (-1)^((a-1)/2 * (b-1)/2) * J(b | a) :=
    quadratic_reciprocity h_odd_a hb
  rw [ha] at h_quad_recip
  simp at h_quad_recip
  have h_pow_neg_one : (-1)^((a-1)/2) = 1 := by
    rw [ha]
    simp
  rw [h_pow_neg_one] at h_quad_recip
  simp at h_quad_recip
  exact h_quad_recip

/- ACTUAL PROOF OF jacobiSym.quadratic_reciprocity_one_mod_four -/

example {a b : ℕ} (ha : a % 4 = 1) (hb : Odd b) :
    J(a | b) = J(b | a) := by
  rw [quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb, pow_mul,
    neg_one_pow_div_two_of_one_mod_four ha, one_pow, one_mul]
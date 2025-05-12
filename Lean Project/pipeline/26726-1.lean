import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open jacobiSym
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example {a b : ℕ} (ha : a % 4 = 1) (hb : Odd b) :
    J(a | b) = J(b | a) := by
  have a_odd : Odd a := by
    rw [← Nat.mod_add_div a 4] at ha
    simp only [ha, Nat.one_add_div_eq_zero, Nat.odd_iff, Nat.even_iff]
    exact ⟨1, rfl⟩
  rw [jacobiSym.quadratic_reciprocity a_odd hb]
  have : (-1) ^ ((a - 1) / 2 * (b - 1) / 2) = 1 := by
    rw [Nat.sub_eq_iff_eq_add] at ha
    have : a = 4 * _ + 1 := ha
    rw [this, Nat.mul_div_cancel_left _ (by linarith)]
    simp only [Nat.div_self (by linarith), pow_one, one_mul, pow_one]
  rw [this, one_mul]

/- ACTUAL PROOF OF jacobiSym.quadratic_reciprocity_one_mod_four -/

example {a b : ℕ} (ha : a % 4 = 1) (hb : Odd b) :
    J(a | b) = J(b | a) := by
  rw [quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb, pow_mul,
    neg_one_pow_div_two_of_one_mod_four ha, one_pow, one_mul]
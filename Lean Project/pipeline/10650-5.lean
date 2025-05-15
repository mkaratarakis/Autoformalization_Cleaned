import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

open legendreSym
open Nat
variable (p : ℕ) [Fact p.Prime]
open ZMod
variable (p : ℕ) [Fact p.Prime]

example (a : ℤ) : (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2) := by
  by_cases hp2 : p = 2
  · subst hp2
    by_cases ha : a ≡ 0 [ZMOD 2]
    · simp [ha, legendreSym]
      have : (0 : ZMod 2) ^ (2 / 2) = 0 := by rfl
      rw [this]
    · have ha' : a ≠ 0 := by
        intro h
        apply ha
        rw [h]
        exact (ZMod.cast_zero 2).symm
      rw [legendreSym, quadraticChar_eq_one_of_char_two]
      · simp
      · exact ha'
      · exact (by decide : 2 ≠ 0)
  · have hodd : ringChar (ZMod p) ≠ 2 := by
      intro h
      apply hp2
      rw [ringChar_zmod_n, Nat.cast_inj] at h
      exact h.symm
    by_cases ha : a ≡ 0 [ZMOD p]
    · simp [ha]
    · have ha' : (a : ZMod p) ≠ 0 := by
        intro h
        apply ha
        rw [h]
        exact (ZMod.cast_zero p).symm
      rw [legendreSym, quadraticChar_eq_pow_of_char_ne_two hodd ha']
      · exact (ZMod.cast_one _).symm
      · exact ha'

/- ACTUAL PROOF OF legendreSym.eq_pow -/

example (a : ℤ) : (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2) := by
  rcases eq_or_ne (ringChar (ZMod p)) 2 with hc | hc
  · by_cases ha : (a : ZMod p) = 0
    · rw [legendreSym, ha, quadraticChar_zero,
        zero_pow (Nat.div_pos (@Fact.out p.Prime).two_le (succ_pos 1)).ne']
      norm_cast
    · have := (ringChar_zmod_n p).symm.trans hc
      -- p = 2
      subst p
      rw [legendreSym, quadraticChar_eq_one_of_char_two hc ha]
      revert ha
      push_cast
      generalize (a : ZMod 2) = b; fin_cases b
      · tauto
      · simp
  · convert quadraticChar_eq_pow_of_char_ne_two' hc (a : ZMod p)
    exact (card p).symm
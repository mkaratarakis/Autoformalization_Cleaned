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
      rw [Int.cast_ofNat, Nat.cast_zero, ZMod.int_cast_zmod_int_cast]
      norm_num
    · have ha' : a ≡ 1 [ZMOD 2] := by
        apply ZMod.int_cast_zmod_int_cast_injective
        rw [ha]
        tauto
      simp [ha', legendreSym]
      rw [Int.cast_ofNat, Nat.cast_one, ZMod.int_cast_zmod_int_cast]
      norm_num
  · have hp_odd : ¬ringChar (ZMod p) = 2 := by
      intro h
      have := @Fintype.card_zmod_eq (ZMod p) _ _
      rw [h, Fintype.card_zmod_eq_two] at this
      norm_num at this
    simp [legendreSym, quadraticChar_eq_pow_of_char_ne_two' hp_odd a]

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
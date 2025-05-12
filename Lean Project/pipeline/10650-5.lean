import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

open legendreSym
open Nat
variable (p : ℕ) [Fact p.Prime]
open ZMod
variable (p : ℕ) [Fact p.Prime]

example (a : ℤ) : (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2) := by
  by_cases hp : p = 2
  · subst hp
    by_cases ha : a ≡ 0 [ZMOD 2]
    · simp only [ha, legendreSym, Int.cast_ofNat_of_le (le_of_lt (by decide : (0:ℕ) < 2)), Int.cast_zero, zero_pow (by decide : 0 < 2 / 2), eq_self_iff_true, iff_true]
    · have : (a : ZMod 2) = 1 := by
        apply Int.cast_ofNat_of_le (le_of_lt (by decide : (0:ℕ) < 2))
        exact Or.resolve_right ha (by decide : (1:ℤ) ≡ 0 [ZMOD 2])
      simp only [legendreSym, this, one_pow (by decide : 0 < 2 / 2), eq_self_iff_true, iff_true]
  · have h₀ : ¬ringChar (ZMod p) = 2 := by
      rw [ringChar_zmod_n, Nat.cast_inj]
      exact hp
    have h₁ := quadraticChar_eq_pow_of_char_ne_two h₀
    by_cases ha : a ≡ 0 [ZMOD p]
    · simp only [ha, legendreSym, Int.cast_zero, zero_pow (Nat.div_pos (Nat.zero_lt_succ _) two_pos), eq_self_iff_true, iff_true]
    · apply h₁
      rwa [Ne.def, Int.cast_eq_zero]

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
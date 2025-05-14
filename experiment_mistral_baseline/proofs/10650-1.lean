import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

open legendreSym
open Nat
variable (p : ℕ) [Fact p.Prime]
open ZMod
variable (p : ℕ) [Fact p.Prime]

example (a : ℤ) : (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2) := by
  cases hp : p with
  | zero =>
    -- Case 1: The characteristic of ℤ/pℤ is 2
    cases hp_prime : Fact.rec Nat.prime_def_eq_two hp.2 with
    | inl h =>
      -- Subcase 1.1: a ≡ 0 (mod p)
      rw [legendreSym_def, ZMod.int_cast_zmod_eq_zero_iff]
      split
      · intro h
        rw [h, ZMod.int_cast_zmod_eq_zero_iff]
        exact ⟨0, rfl⟩
      · rintro ⟨b, rfl⟩
        exact ZMod.int_cast_zmod_eq_zero_iff.1 rfl
    | inr h =>
      -- Subcase 1.2: a ≢ 0 (mod p)
      rw [legendreSym_def, ZMod.int_cast_zmod_eq_one_iff]
      split
      · intro h
        rw [h, ZMod.int_cast_zmod_eq_one_iff]
        exact ⟨1, rfl⟩
      · rintro ⟨b, rfl⟩
        exact ZMod.int_cast_zmod_eq_one_iff.1 rfl
  | succ p =>
    -- Case 2: The characteristic of ℤ/pℤ is not 2
    rw [legendreSym_def, ZMod.int_cast_zmod_pow]
    exact quadratic_char_prop p a

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
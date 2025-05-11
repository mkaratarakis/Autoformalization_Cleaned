import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Legendre symbol

This file contains results about Legendre symbols.

We define the Legendre symbol $\Bigl(\frac{a}{p}\Bigr)$ as `legendreSym p a`.
Note the order of arguments! The advantage of this form is that then `legendreSym p`
is a multiplicative map.

The Legendre symbol is used to define the Jacobi symbol, `jacobiSym a b`, for integers `a`
and (odd) natural numbers `b`, which extends the Legendre symbol.

## Main results

We also prove the supplementary laws that give conditions for when `-1`
is a square modulo a prime `p`:
`legendreSym.at_neg_one` and `ZMod.exists_sq_eq_neg_one_iff` for `-1`.

See `NumberTheory.LegendreSymbol.QuadraticReciprocity` for the conditions when `2` and `-2`
are squares:
`legendreSym.at_two` and `ZMod.exists_sq_eq_two_iff` for `2`,
`legendreSym.at_neg_two` and `ZMod.exists_sq_eq_neg_two_iff` for `-2`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol
-/


open Nat

section Euler

namespace ZMod

variable (p : ℕ) [Fact p.Prime]

/-- Euler's Criterion: A unit `x` of `ZMod p` is a square if and only if `x ^ (p / 2) = 1`. -/
example (x : (ZMod p)ˣ) : (∃ y : (ZMod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1 := by
  by_cases hc : p = 2
  · subst hc
    simp only [eq_iff_true_of_subsingleton, exists_const]
  · have h₀ := FiniteField.unit_isSquare_iff (by rwa [ringChar_zmod_n]) x
    have hs : (∃ y : (ZMod p)ˣ, y ^ 2 = x) ↔ IsSquare x := by
      rw [isSquare_iff_exists_sq x]
      simp_rw [eq_comm]
    rw [hs]
    rwa [card p] at h₀

/-- Euler's Criterion: a nonzero `a : ZMod p` is a square if and only if `x ^ (p / 2) = 1`. -/
theorem euler_criterion {a : ZMod p} (ha : a ≠ 0) : IsSquare (a : ZMod p) ↔ a ^ (p / 2) = 1 := by
  apply (iff_congr _ (by simp [Units.ext_iff])).mp (euler_criterion_units p (Units.mk0 a ha))
  simp only [Units.ext_iff, sq, Units.val_mk0, Units.val_mul]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by
      rintro rfl
      simp [zero_pow, mul_zero, ne_eq, not_true] at ha
    refine ⟨Units.mk0 y hy, ?_⟩; simp

/-- If `a : ZMod p` is nonzero, then `a^(p/2)` is either `1` or `-1`. -/
theorem pow_div_two_eq_neg_one_or_one {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 := by
  rcases Prime.eq_two_or_odd (@Fact.out p.Prime _) with hp2 | hp_odd
  · subst p; revert a ha; intro a; fin_cases a
    · tauto
    · simp
  rw [← mul_self_eq_one_iff, ← pow_add, ← two_mul, two_mul_odd_div_two hp_odd]
  exact pow_card_sub_one_eq_one ha

end ZMod

end Euler

section Legendre

/-!
### Definition of the Legendre symbol and basic properties
-/


open ZMod

variable (p : ℕ) [Fact p.Prime]

/-- The Legendre symbol of `a : ℤ` and a prime `p`, `legendreSym p a`,
is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a` is a nonzero square modulo `p`
* `-1` otherwise.

Note the order of the arguments! The advantage of the order chosen here is
that `legendreSym p` is a multiplicative function `ℤ → ℤ`.
-/
def legendreSym (a : ℤ) : ℤ :=
  quadraticChar (ZMod p) a

namespace legendreSym

/-- We have the congruence `legendreSym p a ≡ a ^ (p / 2) mod p`. -/
theorem eq_pow (a : ℤ) : (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2) := by
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

/-- If `p ∤ a`, then `legendreSym p a` is `1` or `-1`. -/
theorem eq_one_or_neg_one {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    legendreSym p a = 1 ∨ legendreSym p a = -1 :=
  quadraticChar_dichotomy ha

theorem eq_neg_one_iff_not_one {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    legendreSym p a = -1 ↔ ¬legendreSym p a = 1 :=
  quadraticChar_eq_neg_one_iff_not_one ha

/-- The Legendre symbol of `p` and `a` is zero iff `p ∣ a`. -/
theorem eq_zero_iff (a : ℤ) : legendreSym p a = 0 ↔ (a : ZMod p) = 0 :=
  quadraticChar_eq_zero_iff

@[simp]
theorem at_zero : legendreSym p 0 = 0 := by rw [legendreSym, Int.cast_zero, MulChar.map_zero]

@[simp]
theorem at_one : legendreSym p 1 = 1 := by rw [legendreSym, Int.cast_one, MulChar.map_one]

/-- The Legendre symbol is multiplicative in `a` for `p` fixed. -/
protected theorem mul (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  simp [legendreSym, Int.cast_mul, map_mul, quadraticCharFun_mul]

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simps]
def hom : ℤ →*₀ ℤ where
  toFun := legendreSym p
  map_zero' := at_zero p
  map_one' := at_one p
  map_mul' := legendreSym.mul p

theorem legendreSym.mul (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  simp [legendreSym, Int.cast_mul, map_mul, quadraticCharFun_mul]

/- ACTUAL PROOF OF legendreSym.mul -/

example (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  simp [legendreSym, Int.cast_mul, map_mul, quadraticCharFun_mul]
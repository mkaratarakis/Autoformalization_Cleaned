import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open qrSign
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example (m₁ m₂ n : ℕ) : qrSign (m₁ * m₂) n = qrSign m₁ n * qrSign m₂ n := by
  unfold qrSign
  simp only [map_mul, ← ZMod.nat_cast_zmod_eq_nat_cast_int_cast, ZMod.nat_cast_zmod_eq_nat_cast_int_cast_symm, Int.cast_mul, Int.cast_mod, ZMod.int_cast_zmod_eq_int_cast_nat_cast]
  rw [← jacobiSym.mul_right, ← jacobiSym.mul_right]
  exact (jacobiSym.mul_left _ _ _).symm

/- ACTUAL PROOF OF qrSign.mul_left -/

example (m₁ m₂ n : ℕ) : qrSign (m₁ * m₂) n = qrSign m₁ n * qrSign m₂ n := by
  simp_rw [qrSign, Nat.cast_mul, map_mul, jacobiSym.mul_left]
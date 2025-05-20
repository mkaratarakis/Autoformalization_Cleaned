import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open qrSign
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example (m₁ m₂ n : ℕ) : qrSign (m₁ * m₂) n = qrSign m₁ n * qrSign m₂ n := by
  rw [qrSign, qrSign, qrSign]
  simp only [ZMod.val_mul, ZMod.val_cast, ZMod.val_int_cast]
  rw [← ZMod.val_mul (χ₄ m₁) (χ₄ m₂)]
  rw [jacobiSym.mul_left (χ₄ m₁) (χ₄ m₂) n]
  rfl

/- ACTUAL PROOF OF qrSign.mul_left -/

example (m₁ m₂ n : ℕ) : qrSign (m₁ * m₂) n = qrSign m₁ n * qrSign m₂ n := by
  simp_rw [qrSign, Nat.cast_mul, map_mul, jacobiSym.mul_left]
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

open legendreSym
open Nat
variable (p : ℕ) [Fact p.Prime]
open ZMod
variable (p : ℕ) [Fact p.Prime]

example (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  rw [legendreSym, legendreSym, legendreSym]
  simp only [Int.cast_mul, quadraticCharFun_mul]
  exact quadraticCharFun_mul (Int.cast a) (Int.cast b)

/- ACTUAL PROOF OF legendreSym.mul -/

example (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  simp [legendreSym, Int.cast_mul, map_mul, quadraticCharFun_mul]
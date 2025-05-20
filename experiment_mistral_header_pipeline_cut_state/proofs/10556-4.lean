import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

open legendreSym
open Nat
variable (p : ℕ) [Fact p.Prime]
open ZMod
variable (p : ℕ) [Fact p.Prime]

example (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  rw [legendreSym, legendreSym, legendreSym]
  exact (quadraticChar (ZMod p)).map_mul (Int.cast (ZMod p) a) (Int.cast (ZMod p) b)

/- ACTUAL PROOF OF legendreSym.mul -/

example (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  simp [legendreSym, Int.cast_mul, map_mul, quadraticCharFun_mul]
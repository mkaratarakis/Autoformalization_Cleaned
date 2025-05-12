import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

open legendreSym
open Nat
variable (p : ℕ) [Fact p.Prime]
open ZMod
variable (p : ℕ) [Fact p.Prime]

example (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  letI : Fintype (ZMod p) := inferInstance
  letI : DecidableEq (ZMod p) := Classical.decEq _
  have hp2 : ringChar (ZMod p) ≠ 2 := by
    rw [ringChar_ZMod]
    exact Nat.Prime.ne_two p (Nat.prime_iff.mp (Fact.out (inferInstance : Fact p.Prime)))
  have h : quadraticChar (ZMod p) (Int.castRingHom (ZMod p) (a * b)) =
    quadraticChar (ZMod p) (Int.castRingHom (ZMod p) a) * quadraticChar (ZMod p) (Int.castRingHom (ZMod p) b) :=
    quadraticCharFun_mul (Int.castRingHom (ZMod p) a) (Int.castRingHom (ZMod p) b)
  rw [legendreSym, legendreSym, legendreSym]
  exact h

/- ACTUAL PROOF OF legendreSym.mul -/

example (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  simp [legendreSym, Int.cast_mul, map_mul, quadraticCharFun_mul]
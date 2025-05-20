import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

open legendreSym
open Nat
variable (p : ℕ) [Fact p.Prime]
open ZMod
variable (p : ℕ) [Fact p.Prime]

example (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  letI : Fintype (ZMod p) := Fintype.ofEquiv _ (Equiv.ofBijective _ ZMod.val_bijective)
  letI : DecidableEq (ZMod p) := Classical.decEq _
  have hp : ringChar (ZMod p) = p := ringChar_ZMod_eq p
  have hp2 : ringChar (ZMod p) ≠ 2 := by
    rw [hp]
    exact fun h => Nat.Prime.ne_two (Fact.out (inferInstance : Fact p.Prime)) h.symm
  have h : quadraticChar (ZMod p) (Int.castRingHom p (a * b)) =
    quadraticChar (ZMod p) (Int.castRingHom p a) * quadraticChar (ZMod p) (Int.castRingHom p b) :=
    quadraticCharFun_mul (Int.castRingHom p a) (Int.castRingHom p b)
  rw [legendreSym.map_mul, h]

/- ACTUAL PROOF OF legendreSym.mul -/

example (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  simp [legendreSym, Int.cast_mul, map_mul, quadraticCharFun_mul]
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open jacobiSym
open Nat ZMod
open NumberTheorySymbols

example (a : ℤ) : J(a | 0) = 1 := by
  rw [jacobiSym]
  simp only [primeFactorsList_zero, List.pmap, List.prod_nil]
  exact one_zmod 1

/- ACTUAL PROOF OF jacobiSym.zero_right -/

example (a : ℤ) : J(a | 0) = 1 := by
  simp only [jacobiSym, primeFactorsList_zero, List.prod_nil, List.pmap]
import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat

example (x y i : Nat) : (x &&& y).testBit i = (x.testBit i && y.testBit i) := by
  simp only [testBit, Nat.land]
  by_cases h : x.testBit i
  · simp [h]
    by_cases h' : y.testBit i
    · simp [h']
      exact Decidable.true_iff_tt.mpr rfl
    · simp [h']
      exact Decidable.false_iff_ff.mpr rfl
  · simp [h]
    exact Decidable.false_iff_ff.mpr rfl

/- ACTUAL PROOF OF Nat.testBit_and -/

example (x y i : Nat) : (x &&& y).testBit i = (x.testBit i && y.testBit i) := by
  simp [HAnd.hAnd, AndOp.and, land, testBit_bitwise ]
import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (x : Nat) : testBit x 0 = decide (x % 2 = 1) := by
  cases h : x % 2
  · simp [testBit]
    exact decide_eq_false (by simp)
  · simp [testBit]
    simp [Nat.mod_eq_of_lt]
    exact decide_eq_true (by simp)

/- ACTUAL PROOF OF Nat.testBit_zero -/

example (x : Nat) : testBit x 0 = decide (x % 2 = 1) := by
  cases mod_two_eq_zero_or_one x with | _ p => simp [testBit, p]
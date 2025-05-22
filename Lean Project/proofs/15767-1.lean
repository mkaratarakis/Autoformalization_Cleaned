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
    rw [Nat.mod_eq_of_lt (Nat.zero_lt_two : 0 < 2)]
    simp [Bool.decide_eq_false (by simp [Nat.mod_eq_of_lt (Nat.zero_lt_two : 0 < 2)])]
  · simp [testBit]
    rw [Nat.mod_eq_of_lt (Nat.zero_lt_two : 0 < 2)]
    simp [Bool.decide_eq_true (by simp [Nat.mod_eq_of_lt (Nat.zero_lt_two : 0 < 2)])]

/- ACTUAL PROOF OF Nat.testBit_zero -/

example (x : Nat) : testBit x 0 = decide (x % 2 = 1) := by
  cases mod_two_eq_zero_or_one x with | _ p => simp [testBit, p]
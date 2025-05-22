import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (x : Nat)
    : (!decide (x % 2 = 1)) = decide (x % 2 = 0) := by
  by_cases h: x%2=0
  . simp [h]
  . simp [h]

/- ACTUAL PROOF OF Nat.not_decide_mod_two_eq_one -/

example (x : Nat)
    : (!decide (x % 2 = 1)) = decide (x % 2 = 0) := by
  cases Nat.mod_two_eq_zero_or_one x <;> (rename_i p; simp [p])
import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (n : Nat) : 1 <<< n = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [shiftr, pow_succ]
    exact ih

/- ACTUAL PROOF OF Nat.one_shiftLeft -/

example (n : Nat) : 1 <<< n = 2 ^ n := by
  rw [shiftLeft_eq, Nat.one_mul]
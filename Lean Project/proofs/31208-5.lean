import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n) : 2 * n = n + n := by
  rw [show 2 = 1 + 1 from rfl]
  rw [add_mul]
  rw [one_mul]
  rw [add_comm]

/- ACTUAL PROOF OF Nat.two_mul -/

example (n) : 2 * n = n + n := by
  rw [Nat.succ_mul, Nat.one_mul]
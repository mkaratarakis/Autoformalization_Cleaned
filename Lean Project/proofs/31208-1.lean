import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n) : 2 * n = n + n := by
  rw [←add_succ_sub_one 1]
  rw [add_mul]
  rw [one_mul]
  rfl

/- ACTUAL PROOF OF Nat.two_mul -/

example (n) : 2 * n = n + n := by
  rw [Nat.succ_mul, Nat.one_mul]
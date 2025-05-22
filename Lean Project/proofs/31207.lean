import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n) : n * 2 = n + n := by
  rw [mul_succ]
  simp

/- ACTUAL PROOF OF Nat.mul_two -/

example (n) : n * 2 = n + n := by
  rw [Nat.mul_succ, Nat.mul_one]
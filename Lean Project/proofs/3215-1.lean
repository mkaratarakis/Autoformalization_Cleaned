import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (H : 0 < n) : n / n = 1 := by
  let t := Nat.div_self (n)
  rw [Nat.div_eq_sub_mul_div]
  rw [Nat.mul_one]
  rw [Nat.sub_zero]

/- ACTUAL PROOF OF Nat.div_self -/

example (H : 0 < n) : n / n = 1 := by
  let t := add_div_right 0 H
  rwa [Nat.zero_add, Nat.zero_div] at t
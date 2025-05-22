import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (H : 0 < n) : n / n = 1 := by
  rw [div_eq_of_lt]
  . apply Nat.lt_of_lt_of_le H (Nat.le_refl _)
  . rfl

/- ACTUAL PROOF OF Nat.div_self -/

example (H : 0 < n) : n / n = 1 := by
  let t := add_div_right 0 H
  rwa [Nat.zero_add, Nat.zero_div] at t
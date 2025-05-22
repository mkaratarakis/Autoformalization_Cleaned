import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by
  rw [← Nat.zero_add (m * n)]
  rw [Nat.add_mul_div_right _ _ H]
  rw [Nat.zero_div _ H]
  rw [Nat.zero_add]

/- ACTUAL PROOF OF Nat.mul_div_cancel -/

example (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by
  let t := add_mul_div_right 0 m H
  rwa [Nat.zero_add, Nat.zero_div, Nat.zero_add] at t
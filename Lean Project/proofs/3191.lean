import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (n : Nat) : n / 0 = 0 := by
  simp [Nat.div]
  exact Nat.zero_div n

/- ACTUAL PROOF OF Nat.div_zero -/

example (n : Nat) : n / 0 = 0 := by
  rw [div_eq]; simp [Nat.lt_irrefl]
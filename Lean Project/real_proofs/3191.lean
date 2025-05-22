import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat



example (n : Nat) : n / 0 = 0 := by
  rw [div_eq]; simp [Nat.lt_irrefl]
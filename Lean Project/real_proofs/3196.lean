import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat



example (m k : Nat) : m % k = m - k * (m / k) := by
  rw [Nat.sub_eq_of_eq_add]
  apply (Nat.mod_add_div _ _).symm
import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat



example (x z : Nat) : (x + z) % z = x % z := by
  rw [mod_eq_sub_mod (Nat.le_add_left ..), Nat.add_sub_cancel]
import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat



example (n : Nat) : n % n = 0 := by
  rw [mod_eq_sub_mod (Nat.le_refl _), Nat.sub_self, zero_mod]
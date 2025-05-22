import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (n : Nat) : n % n = 0 := by
  simp [Nat.mod_eq_of_lt]
  simp [sub_self]
  simp [zero_mod]

/- ACTUAL PROOF OF Nat.mod_self -/

example (n : Nat) : n % n = 0 := by
  rw [mod_eq_sub_mod (Nat.le_refl _), Nat.sub_self, zero_mod]
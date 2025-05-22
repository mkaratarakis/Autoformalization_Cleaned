import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a b c : Nat} (h : a = c + b) : a - b = c := by
 rw [h]
 rw [Nat.sub_eq_of_eq_add]

/- ACTUAL PROOF OF Nat.sub_eq_of_eq_add -/

example {a b c : Nat} (h : a = c + b) : a - b = c := by
  rw [h, Nat.add_sub_cancel]
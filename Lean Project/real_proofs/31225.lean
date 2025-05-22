import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example {a b c : Nat} (hle : b ≤ a) (h : a - b = c) : a = c + b := by
  rw [h.symm, Nat.sub_add_cancel hle]
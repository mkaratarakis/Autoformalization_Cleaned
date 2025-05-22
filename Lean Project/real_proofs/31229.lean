import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (n : Nat) : 0 - n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih, Nat.sub_succ]; decide
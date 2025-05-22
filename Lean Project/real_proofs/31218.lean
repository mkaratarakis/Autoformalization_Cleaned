import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example {a b c : Nat} (h : a + b ≤ a + c) : b ≤ c := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    rw [Nat.add_assoc] at hd
    apply Nat.add_left_cancel hd
import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example {a b c : Nat} (hle : b ≤ c) (h : a ≤ c - b) : a + b ≤ c := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    rw [Nat.eq_add_of_sub_eq hle hd.symm]
    simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
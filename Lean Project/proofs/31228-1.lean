import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n : Nat) : n - 1 = n ↔ n = 0 := by
  cases n with
  | zero =>
    simp
  | succ k =>
    simp
    exact Iff.intro (fun h => Nat.noConfusion h) (fun h => Nat.noConfusion h)

/- ACTUAL PROOF OF Nat.sub_one_eq_self -/

example (n : Nat) : n - 1 = n ↔ n = 0 := by
  cases n <;> simp [ne_add_one]
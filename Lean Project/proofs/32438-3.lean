import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) :
    max (min a b) c = min (max a c) (max b c) := by
  rw [max_min_distrib]
  rw [max_comm]

/- ACTUAL PROOF OF Nat.max_min_distrib_right -/

example (a b c : Nat) :
    max (min a b) c = min (max a c) (max b c) := by
  repeat rw [Nat.max_comm _ c]
  exact Nat.max_min_distrib_left ..
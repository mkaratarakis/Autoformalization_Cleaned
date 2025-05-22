import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) :
    min (max a b) c = max (min a c) (min b c) := by
  rw [min_comm (max a b) c]
  rw [min_max_distrib_left]
  rw [min_comm a c]
  rw [min_comm b c]

/- ACTUAL PROOF OF Nat.min_max_distrib_right -/

example (a b c : Nat) :
    min (max a b) c = max (min a c) (min b c) := by
  repeat rw [Nat.min_comm _ c]
  exact Nat.min_max_distrib_left ..
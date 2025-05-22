import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) :
    min (max a b) c = max (min a c) (min b c) := by
  rcases max_eq_left_or_right a b with (h|h)
  · rw [h]
    rfl
  · rw [h]
    rfl

/- ACTUAL PROOF OF Nat.min_max_distrib_right -/

example (a b c : Nat) :
    min (max a b) c = max (min a c) (min b c) := by
  repeat rw [Nat.min_comm _ c]
  exact Nat.min_max_distrib_left ..
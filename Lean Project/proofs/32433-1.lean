import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (x y) : min (succ x) (succ y) = succ (min x y) := by
  cases h: le_total x y with
  | inl h =>
    rw [min_eq_left h, succ_le_succ h]
    rw [min_eq_left (succ_le_succ h)]
  | inr h =>
    rw [min_eq_right h, succ_le_succ h]
    rw [min_eq_right (succ_le_succ h)]

/- ACTUAL PROOF OF Nat.succ_min_succ -/

example (x y) : min (succ x) (succ y) = succ (min x y) := by
  cases Nat.le_total x y with
  | inl h => rw [Nat.min_eq_left h, Nat.min_eq_left (Nat.succ_le_succ h)]
  | inr h => rw [Nat.min_eq_right h, Nat.min_eq_right (Nat.succ_le_succ h)]
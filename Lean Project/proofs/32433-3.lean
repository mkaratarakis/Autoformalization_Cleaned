import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (x y) : min (succ x) (succ y) = succ (min x y) := by
  by_cases h : x ≤ y
  · have : succ x ≤ succ y := Nat.succ_le_succ h
    rw [min_def, if_pos this]
    rw [min_def, if_pos h]
    rfl
  · push_neg at h
    have : y < x := h
    have : succ y ≤ succ x := Nat.succ_le_succ (le_of_lt this)
    rw [min_def, if_neg (not_le_of_gt this)]
    rw [min_def, if_neg (not_le.mpr (not_le_of_gt this))]
    rfl

/- ACTUAL PROOF OF Nat.succ_min_succ -/

example (x y) : min (succ x) (succ y) = succ (min x y) := by
  cases Nat.le_total x y with
  | inl h => rw [Nat.min_eq_left h, Nat.min_eq_left (Nat.succ_le_succ h)]
  | inr h => rw [Nat.min_eq_right h, Nat.min_eq_right (Nat.succ_le_succ h)]
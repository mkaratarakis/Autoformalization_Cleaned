import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat



example (x y) : max (succ x) (succ y) = succ (max x y) := by
  cases Nat.le_total x y with
  | inl h => rw [Nat.max_eq_right h, Nat.max_eq_right (Nat.succ_le_succ h)]
  | inr h => rw [Nat.max_eq_left h, Nat.max_eq_left (Nat.succ_le_succ h)]
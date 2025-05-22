import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (n m : Nat) : n - m = n - min n m := by
  cases decLe : decLe n m with
  | isTrue h =>
    rw [min_eq_left h]
    rfl
  | isFalse h =>
    rw [min_eq_right h]
    rw [Nat.sub_self]
    rfl

/- ACTUAL PROOF OF Nat.sub_eq_sub_min -/

example (n m : Nat) : n - m = n - min n m := by
  cases Nat.le_total n m with
  | inl h => rw [Nat.min_eq_left h, Nat.sub_eq_zero_of_le h, Nat.sub_self]
  | inr h => rw [Nat.min_eq_right h]
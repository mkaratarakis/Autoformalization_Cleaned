import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : max (a * b) (a * c) = a * max b c := by
  unfold max
  cases le_total b c with
  | inl h =>
    rw [dif_pos h]
    rw [dif_pos (mul_le_mul_left' a h)]

  | inr h =>
    rw [dif_neg h]
    rw [dif_neg (mul_le_mul_left' a (le_of_not_le h))]

/- ACTUAL PROOF OF Nat.mul_max_mul_left -/

example (a b c : Nat) : max (a * b) (a * c) = a * max b c := by
  repeat rw [Nat.mul_comm a]
  exact Nat.mul_max_mul_right ..
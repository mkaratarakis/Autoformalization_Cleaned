import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat



example (m : Nat) : lcm m m = m := by
  match eq_zero_or_pos m with
  | .inl h => rw [h, lcm_zero_left]
  | .inr h => simp [lcm, Nat.mul_div_cancel _ h]
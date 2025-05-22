import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat


example (m : Nat) : lcm m m = m := by
  cases m with
  | zero =>
    show lcm 0 0 = 0
    rw [lcm_zero_left]
  | succ n =>
    show lcm (succ n) (succ n) = succ n
    rw [lcm_self]

/- ACTUAL PROOF OF Nat.lcm_self -/

example (m : Nat) : lcm m m = m := by
  match eq_zero_or_pos m with
  | .inl h => rw [h, lcm_zero_left]
  | .inr h => simp [lcm, Nat.mul_div_cancel _ h]
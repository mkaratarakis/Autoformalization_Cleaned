import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a n m : Nat} (h : 1 < a) (w : n ≤ m) : a ^ n ≤ a ^ m := by
  cases w
  case refl =>
    exact Nat.le_refl (a ^ n)
  case step m w =>
    have : a ^ n ≤ a ^ m := Nat.le_step w
    rw [pow_succ]
    exact Nat.mul_le_mul_left this a (Nat.one_lt_iff_ne_zero.mpr h)

/- ACTUAL PROOF OF Nat.pow_le_pow_of_le -/

example {a n m : Nat} (h : 1 < a) (w : n ≤ m) : a ^ n ≤ a ^ m := by
  cases Nat.lt_or_eq_of_le w
  case inl lt =>
    exact Nat.le_of_lt (Nat.pow_lt_pow_of_lt h lt)
  case inr eq =>
    subst eq
    exact Nat.le_refl _
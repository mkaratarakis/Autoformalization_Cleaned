import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a n m : Nat} (h : 1 < a) (w : n ≤ m) : a ^ n ≤ a ^ m := by
  cases w
  case refl =>
    exact le_rfl
  case step m w =>
    have : a ^ n * a ≤ a ^ m.succ * a :=
      calc
        a ^ n * a ≤ a ^ m * a := Nat.mul_le_mul_right (le_step w) a
        _ = a ^ m.succ * a := by rw [pow_succ]
    exact this

/- ACTUAL PROOF OF Nat.pow_le_pow_of_le -/

example {a n m : Nat} (h : 1 < a) (w : n ≤ m) : a ^ n ≤ a ^ m := by
  cases Nat.lt_or_eq_of_le w
  case inl lt =>
    exact Nat.le_of_lt (Nat.pow_lt_pow_of_lt h lt)
  case inr eq =>
    subst eq
    exact Nat.le_refl _
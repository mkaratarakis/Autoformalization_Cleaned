import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat



example {m n : Nat} (a : Nat) (h : m ≤ n) : a ^ m ∣ a ^ n := by
  cases Nat.exists_eq_add_of_le h
  case intro k p =>
    subst p
    rw [Nat.pow_add]
    apply Nat.dvd_mul_right
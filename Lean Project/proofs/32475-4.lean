import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {m n : Nat} (a : Nat) (h : m ≤ n) : a ^ m ∣ a ^ n := by
  obtain k := Nat.sub_add_cancel h
  rw [←k, ←pow_add']
  exact dvd_mul_right _ _

/- ACTUAL PROOF OF Nat.pow_dvd_pow -/

example {m n : Nat} (a : Nat) (h : m ≤ n) : a ^ m ∣ a ^ n := by
  cases Nat.exists_eq_add_of_le h
  case intro k p =>
    subst p
    rw [Nat.pow_add]
    apply Nat.dvd_mul_right
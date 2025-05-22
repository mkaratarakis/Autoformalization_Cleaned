import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat


example {m n : Nat} (H : n % m = 0) : m ∣ n := by
  exists n / m
  rw [Nat.add_mul_mod_self]
  rw [H]
  rw [zero_add]

/- ACTUAL PROOF OF Nat.dvd_of_mod_eq_zero -/

example {m n : Nat} (H : n % m = 0) : m ∣ n := by
  exists n / m
  have := (mod_add_div n m).symm
  rwa [H, Nat.zero_add] at this
import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat


example {n m : Nat} (H : n ∣ m) : m / n * n = m := by
  obtain ⟨k, hk⟩ := H
  rw [hk]
  rw [Nat.div_eq_of_lt]
  · simp
  · exact Nat.zero_le k

/- ACTUAL PROOF OF Nat.div_mul_cancel -/

example {n m : Nat} (H : n ∣ m) : m / n * n = m := by
  rw [Nat.mul_comm, Nat.mul_div_cancel' H]
import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat


example {n m : Nat} (H : n ∣ m) : m / n * n = m := by
  have k := dvd.elim H
  calc
    m / n * n = k * n / n * n := by rw [div_mul_cancel]
    _ = k * n := by rfl
    _ = m := by rw [mul_comm]

/- ACTUAL PROOF OF Nat.div_mul_cancel -/

example {n m : Nat} (H : n ∣ m) : m / n * n = m := by
  rw [Nat.mul_comm, Nat.mul_div_cancel' H]
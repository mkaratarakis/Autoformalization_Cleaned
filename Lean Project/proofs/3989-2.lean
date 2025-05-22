import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat


example (m : Nat) (H : k ∣ n) : m * n / k = m * (n / k) := by
  have h1 : m * n / k = m * (n / k * k) / k := by
    rw [←mul_assoc]
    rw [Nat.mul_div_cancel _ (dvd_trans H (dvd_refl k))]
  rw [h1]
  rw [←Nat.mul_div_assoc]
  rw [Nat.mul_div_cancel _ (dvd_trans H (dvd_refl k))]

/- ACTUAL PROOF OF Nat.mul_div_assoc -/

example (m : Nat) (H : k ∣ n) : m * n / k = m * (n / k) := by
  match Nat.eq_zero_or_pos k with
  | .inl h0 => rw [h0, Nat.div_zero, Nat.div_zero, Nat.mul_zero]
  | .inr hpos =>
    have h1 : m * n / k = m * (n / k * k) / k := by rw [Nat.div_mul_cancel H]
    rw [h1, ← Nat.mul_assoc, Nat.mul_div_cancel _ hpos]
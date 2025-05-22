import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat


example 
    (kpos : 0 < k) (H : k * m ∣ k * n) : m ∣ n := by
  rcases H with ⟨l, hl⟩
  rw [← mul_assoc, ← mul_assoc, mul_left_cancel₀ kpos] at hl
  use l
  exact hl

/- ACTUAL PROOF OF Nat.dvd_of_mul_dvd_mul_left -/

example 
    (kpos : 0 < k) (H : k * m ∣ k * n) : m ∣ n := by
  let ⟨l, H⟩ := H
  rw [Nat.mul_assoc] at H
  exact ⟨_, Nat.eq_of_mul_eq_mul_left kpos H⟩
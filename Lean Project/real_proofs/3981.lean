import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat



example 
    (kpos : 0 < k) (H : k * m ∣ k * n) : m ∣ n := by
  let ⟨l, H⟩ := H
  rw [Nat.mul_assoc] at H
  exact ⟨_, Nat.eq_of_mul_eq_mul_left kpos H⟩
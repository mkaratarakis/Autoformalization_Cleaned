import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat


example {m n : Nat} (H : m ∣ n) : n % m = 0 := by
  obtain ⟨k, hk⟩ := H
  rw [hk]
  exact mod_eq_of_dvd (dvd_mul_left _ _)

/- ACTUAL PROOF OF Nat.mod_eq_zero_of_dvd -/

example {m n : Nat} (H : m ∣ n) : n % m = 0 := by
  let ⟨z, H⟩ := H; rw [H, mul_mod_right]
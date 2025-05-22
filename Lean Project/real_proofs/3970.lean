import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat



example {m n : Nat} (H : m ∣ n) : n % m = 0 := by
  let ⟨z, H⟩ := H; rw [H, mul_mod_right]
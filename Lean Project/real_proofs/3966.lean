import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat



example {k m n : Nat} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n := by
  rw [Nat.add_comm]; exact Nat.dvd_add_iff_right h
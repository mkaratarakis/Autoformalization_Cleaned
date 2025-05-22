import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat


example {k m n : Nat} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n := by
  rw [add_comm]
  exact dvd_add_iff_right h

/- ACTUAL PROOF OF Nat.dvd_add_iff_left -/

example {k m n : Nat} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n := by
  rw [Nat.add_comm]; exact Nat.dvd_add_iff_right h
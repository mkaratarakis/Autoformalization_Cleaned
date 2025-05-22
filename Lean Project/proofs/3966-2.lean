import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat


example {k m n : Nat} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n := by
  constructor
  · intro hm
    apply dvd_add
    · exact hm
    · exact h
  · intro hmn
    apply dvd_of_dvd_add_right
    · exact hmn
    · exact h

/- ACTUAL PROOF OF Nat.dvd_add_iff_left -/

example {k m n : Nat} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n := by
  rw [Nat.add_comm]; exact Nat.dvd_add_iff_right h
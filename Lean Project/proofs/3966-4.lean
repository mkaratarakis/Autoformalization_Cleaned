import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat


example {k m n : Nat} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n := by
  constructor
  · intro hm
    obtain ⟨a, rfl⟩ := h
    obtain ⟨b, rfl⟩ := hm
    use b + a
    rfl
  · intro hmn
    obtain ⟨a, rfl⟩ := h
    obtain ⟨b, hmn⟩ := hmn
    use b - a
    rw [add_sub_cancel_right]
    exact hmn

/- ACTUAL PROOF OF Nat.dvd_add_iff_left -/

example {k m n : Nat} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n := by
  rw [Nat.add_comm]; exact Nat.dvd_add_iff_right h
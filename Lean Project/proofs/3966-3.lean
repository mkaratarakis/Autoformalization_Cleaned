import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat


example {k m n : Nat} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n := by
  constructor
  · intro hm
    obtain ⟨a, rfl⟩ := h
    obtain ⟨b, rfl⟩ := hm
    use a + b
    rfl
  · intro hmn
    obtain ⟨a, h_eq⟩ := h
    obtain ⟨b, hmn_eq⟩ := hmn
    rw [h_eq] at hmn_eq
    rw [hmn_eq]
    rw [Nat.add_sub_cancel_left]
    use b

/- ACTUAL PROOF OF Nat.dvd_add_iff_left -/

example {k m n : Nat} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n := by
  rw [Nat.add_comm]; exact Nat.dvd_add_iff_right h
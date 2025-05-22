import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a b c : Nat} (h : a - b ≤ c) : a ≤ c + b := by
  by_cases h1 : a ≤ b
  · exact le_trans h1 (le_add_right le_rfl c)
  · have h2 : b ≤ a := le_of_not_le h1
    have h3 : a - b + b = a := sub_add_cancel h2
    rw [h3] at h
    exact le_add_right h c

/- ACTUAL PROOF OF Nat.le_add_of_sub_le -/

example {a b c : Nat} (h : a - b ≤ c) : a ≤ c + b := by
  match le.dest h, Nat.le_total a b with
  | _, Or.inl hle =>
    exact Nat.le_trans hle (Nat.le_add_left ..)
  | ⟨d, hd⟩, Or.inr hge =>
    apply @le.intro _ _ d
    rw [Nat.add_comm, ← Nat.add_sub_assoc hge] at hd
    have hd := Nat.eq_add_of_sub_eq (Nat.le_trans hge (Nat.le_add_left ..)) hd
    rw [Nat.add_comm, hd]
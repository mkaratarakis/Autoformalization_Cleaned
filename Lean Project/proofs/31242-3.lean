import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a b c : Nat} (h : a - b ≤ c) : a ≤ c + b := by
  by_cases h1 : a ≤ b
  · apply Nat.le_trans h1
    simp [Nat.add_comm, Nat.le_add_left]
  · have h2 : b ≤ a := not_le.1 h1
    calc
      a = (a - b) + b := (Nat.sub_add_cancel h2).symm
      _ ≤ c + b := Nat.add_le_add_right h _

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
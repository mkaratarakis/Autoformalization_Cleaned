import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a b c : Nat} (h : a - b ≤ c) : a ≤ c + b := by
  cases hlt : le_total a b with
  | inl h1 =>
    have h2 : b ≤ c + b := le_add_left le_rfl
    exact le_trans h1 h2
  | inr h1 =>
    have h2 : a - b + b = a := sub_add_cancel h1
    rw [h2] at h
    rw [add_comm c b] at h
    exact le_add_right h

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
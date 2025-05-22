import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a b c : Nat} (h : a ≤ c + b) : a - b ≤ c := by
  by_cases h1 : a ≤ b
  · rw [Nat.sub_eq_zero_of_le h1]
    exact Nat.zero_le c
  · have h2 : b ≤ a := Nat.le_of_not_le h1
    have h3 : a - b + b = a := by simp
    rw [← h3]
    apply Nat.le_add_left
    apply Nat.le_of_add_le_left
    rw [Nat.add_comm]
    exact h

/- ACTUAL PROOF OF Nat.sub_le_of_le_add -/

example {a b c : Nat} (h : a ≤ c + b) : a - b ≤ c := by
  match le.dest h, Nat.le_total a b with
  | _, Or.inl hle =>
    rw [Nat.sub_eq_zero_of_le hle]
    apply Nat.zero_le
  | ⟨d, hd⟩, Or.inr hge =>
    apply @le.intro _ _ d
    have hd := Nat.sub_eq_of_eq_add hd
    rw [Nat.add_comm, ← Nat.add_sub_assoc hge, Nat.add_comm]
    exact hd
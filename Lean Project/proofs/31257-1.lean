import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a b c : Nat} (h : a ≤ c + b) : a - b ≤ c := by
  cases le_or_gt a b with
  | inl h1 =>
    rw [Nat.sub_eq_zero_of_le h1]
    exact Nat.zero_le c
  | inr h1 =>
    have h2 : ∃ d, a + d = c + b := exists_eq_add_of_le h
    rcases h2 with ⟨d, h3⟩
    rw [Nat.add_sub_cancel_left]
    calc
      a - b + d = d + (a - b) := by rw [Nat.add_comm]
      _ = d + a - b := by rw [Nat.add_sub_assoc]
      _ = a + d - b := by rw [Nat.add_comm]
      _ = c := by rw [h3, Nat.add_sub_cancel_left]

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
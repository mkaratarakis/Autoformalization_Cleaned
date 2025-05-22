import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



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
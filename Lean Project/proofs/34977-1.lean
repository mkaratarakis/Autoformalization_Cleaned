import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {n : Nat} {a : α} {l : List α} : replicate n a ⊆ l ↔ n = 0 ∨ a ∈ l := by
  induction n with
  | zero =>
    simp [replicate]
    constructor
    · intro h
      right
      exact h
    · intro h
      cases h
      · simp
      · exact h
  | succ k ih =>
    simp [replicate]
    constructor
    · intro h
      cases h
      · apply Or.inr
        exact h
      · apply Or.inl
        apply Nat.succ_ne_zero
    · intro h
      cases h
      · simp at h
      · apply Sublist.cons
        · exact h
        · apply ih
          right
          exact h

/- ACTUAL PROOF OF List.replicate_subset -/

example {n : Nat} {a : α} {l : List α} : replicate n a ⊆ l ↔ n = 0 ∨ a ∈ l := by
  induction n with
  | zero => simp
  | succ n ih => simp (config := {contextual := true}) [replicate_succ, ih, cons_subset]
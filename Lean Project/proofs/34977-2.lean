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
    apply Iff.intro
    · intro h
      exact Or.inl rfl
    · intro h
      cases h
      · trivial
      · trivial
  | succ k ih =>
    simp [replicate]
    apply Iff.intro
    · intro h
      cases h
      · exact Or.inr h
      · exact Or.inl (Nat.succ_ne_zero _)
    · intro h
      cases h
      · exfalso
        exact Nat.noConfusion h
      · apply Sublist.cons _ (ih (Or.inr h))
        exact h

/- ACTUAL PROOF OF List.replicate_subset -/

example {n : Nat} {a : α} {l : List α} : replicate n a ⊆ l ↔ n = 0 ∨ a ∈ l := by
  induction n with
  | zero => simp
  | succ n ih => simp (config := {contextual := true}) [replicate_succ, ih, cons_subset]
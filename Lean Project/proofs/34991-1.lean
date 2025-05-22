import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {m n} (a : α) :
    replicate m a <+ replicate n a ↔ m ≤ n := by
  constructor
  · intro h
    rw [← length_replicate, ← length_replicate] at h
    exact Sublist.length_le_of_sublist h
  · intro h
    induction n with
    | zero =>
      simp [replicate]
    | succ n ih =>
      apply Sublist.cons _ ih
      simp [replicate]

/- ACTUAL PROOF OF List.replicate_sublist_replicate -/

example {m n} (a : α) :
    replicate m a <+ replicate n a ↔ m ≤ n := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.length_le; simp only [length_replicate] at this ⊢; exact this
  · induction h with
    | refl => apply Sublist.refl
    | step => simp [*, replicate, Sublist.cons]
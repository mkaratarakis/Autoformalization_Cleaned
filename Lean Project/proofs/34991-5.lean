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
    have hlen : m ≤ n := by
      apply Nat.le_of_lt_or_eq
      calc
        m = (replicate m a).length := (length_replicate m a).symm
        _ ≤ (replicate n a).length := Sublist.length_le_of_sublist h
        _ = n := length_replicate n a
    exact hlen
  · intro h
    induction n with
    | zero =>
      simp [replicate, Nat.le_zero] at h
      exact Sublist.refl []
    | succ n ih =>
      by_cases hle : m ≤ n
      · exact ih hle
      · have hm : m = n + 1 := by
          apply Nat.eq_of_le_of_not_lt h
          simpa [Nat.not_le_of_lt] using hle
        rw [hm]
        simp [replicate]
        exact Sublist.refl (replicate (n + 1) a)

/- ACTUAL PROOF OF List.replicate_sublist_replicate -/

example {m n} (a : α) :
    replicate m a <+ replicate n a ↔ m ≤ n := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.length_le; simp only [length_replicate] at this ⊢; exact this
  · induction h with
    | refl => apply Sublist.refl
    | step => simp [*, replicate, Sublist.cons]
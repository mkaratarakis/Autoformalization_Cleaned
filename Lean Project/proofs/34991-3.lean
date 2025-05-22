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
      have : m = (replicate m a).length := by rfl
      have : n = (replicate n a).length := by rfl
      rw [this, this]
      exact Sublist.length_le_of_sublist h
    exact hlen
  · intro h
    induction n with
    | zero =>
      simp [replicate]
      exact (m_eq_zero_of_m_le_zero h).symm
    | succ n ih =>
      by_cases hle : m ≤ n
      · exact ih hle
      · have hm : m = n + 1 := by
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
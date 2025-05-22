import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {L : List (List α)} {l} (h : l ∈ L) : l <+ L.flatten := by
  induction L generalizing l with
  | nil =>
    exfalso
    apply List.not_mem_nil l h
  | cons hd tl ih =>
    cases h with
    | head h =>
      apply Sublist.refl
    | tail h =>
      apply Sublist.cons_trans (Sublist.refl _)
      apply ih
      exact h

/- ACTUAL PROOF OF List.sublist_join_of_mem -/

example {L : List (List α)} {l} (h : l ∈ L) : l <+ L.join := by
  induction L with
  | nil => cases h
  | cons l' L ih =>
    rcases mem_cons.1 h with (rfl | h)
    · simp [h]
    · simp [ih h, join_cons, sublist_append_of_sublist_right]
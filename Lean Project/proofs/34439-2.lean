import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l : List α} (h : l.length ≤ i) : take i l = l := by
  have h1 : drop i l = [] := by
    apply drop_eq_nil_of_le
    exact h
  have h2 : take i l ++ drop i l = l := by
    apply take_drop
  rw [h1] at h2
  exact Eq.symm (append_nil _).symm

/- ACTUAL PROOF OF List.take_of_length_le -/

example {l : List α} (h : l.length ≤ i) : take i l = l := by
  have := take_append_drop i l
  rw [drop_of_length_le h, append_nil] at this; exact this
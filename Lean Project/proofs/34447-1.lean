import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {n} {l : List α} (h) : drop n l = get l ⟨n, h⟩ :: drop (n + 1) l := by
  rw [drop]
  simp
  rw [get?_eq]
  simp
  rw [drop]
  simp
  exact h
example {n} {l : List α} (h) : drop n l = get l ⟨n, h⟩ :: drop (n + 1) l := by
  apply example
  exact h

/- ACTUAL PROOF OF List.drop_eq_get_cons -/

example {n} {l : List α} (h) : drop n l = get l ⟨n, h⟩ :: drop (n + 1) l := by
  simp [drop_eq_getElem_cons]
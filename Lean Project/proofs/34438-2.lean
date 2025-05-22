import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (l : List α) (i) : get l i :: drop (i + 1) l = drop i l := by
  induction l generalizing i with
  | nil =>
    cases i
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp
    | succ j =>
      simp
      rw [ih]

/- ACTUAL PROOF OF List.get_cons_drop -/

example (l : List α) (i) : get l i :: drop (i + 1) l = drop i l := by
  simp
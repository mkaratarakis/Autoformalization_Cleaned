import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (l : List α) (i) : get l i :: drop (i + 1) l = drop i l := by
  induction l with
  | nil =>
    cases i
    case mk =>
      simp
      rfl
  | cons hd tl ih =>
    cases i with
    | mk =>
      simp
      rfl
    | succ j =>
      simp
      rw [ih]
      rfl

/- ACTUAL PROOF OF List.get_cons_drop -/

example (l : List α) (i) : get l i :: drop (i + 1) l = drop i l := by
  simp
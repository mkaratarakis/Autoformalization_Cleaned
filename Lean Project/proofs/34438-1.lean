import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (l : List α) (i) : get l i :: drop (i + 1) l = drop i l := by
  rw [getElem_eq_nthLe]
  rw [drop_eq_nthLe]
  rw [drop_eq_nthLe]
  simp

/- ACTUAL PROOF OF List.get_cons_drop -/

example (l : List α) (i) : get l i :: drop (i + 1) l = drop i l := by
  simp
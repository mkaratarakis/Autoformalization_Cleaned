import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example (a : α) (l : List α) : l.erase a = l.eraseP (· == a) := by
  induction l with
  | nil =>
    simp
  | cons b t ih =>
    by_cases hb: b == a
    · simp [hb]
    · have : t.erase a = t.eraseP (· == a) := ih
      simp [hb, this]

/- ACTUAL PROOF OF List.erase_eq_eraseP' -/

example (a : α) (l : List α) : l.erase a = l.eraseP (· == a) := by
  induction l
  · simp
  · next b t ih =>
    rw [erase_cons, eraseP_cons, ih]
    if h : b == a then simp [h] else simp [h]
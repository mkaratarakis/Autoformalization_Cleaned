import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (l) (h : ¬p a) : find? p (a :: l) = find? p l := by
  unfold find?
  simp [h]

/- ACTUAL PROOF OF List.find?_cons_of_neg -/

example (l) (h : ¬p a) : find? p (a :: l) = find? p l := by
  simp [find?, h]
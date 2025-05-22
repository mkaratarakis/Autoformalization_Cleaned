import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (α : Type) (p : α → Bool) (a : α) (l : List α) (h : ¬p a) : find? p (a :: l) = find? p l := by
  simp [find?, h]

/- ACTUAL PROOF OF List.find?_cons_of_neg -/

example (l) (h : ¬p a) : find? p (a :: l) = find? p l := by
  simp [find?, h]
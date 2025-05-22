import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (l) (h : p a) : find? p (a :: l) = some a := by
  unfold find?
  simp [h]

/- ACTUAL PROOF OF List.find?_cons_of_pos -/

example (l) (h : p a) : find? p (a :: l) = some a := by
  simp [find?, h]
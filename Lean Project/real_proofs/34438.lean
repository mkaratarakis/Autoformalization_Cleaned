import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example (l : List α) (i) : get l i :: drop (i + 1) l = drop i l := by
  simp
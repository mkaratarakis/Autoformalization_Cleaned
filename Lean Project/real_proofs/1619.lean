import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat


example (l : List α) (i : Nat) (h : i < l.enum.length) :
    l.enum[i] = (i, l[i]'(by simpa [enum_length] using h)) := by
  simp [enum]
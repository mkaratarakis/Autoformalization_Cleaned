import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat


example (l : List α) (n) (i : Nat) (h : i < (l.enumFrom n).length) :
    (l.enumFrom n)[i] = (n + i, l[i]'(by simpa [enumFrom_length] using h)) := by
  simp only [enumFrom_length] at h
  rw [getElem_eq_getElem?]
  simp only [getElem?_enumFrom, getElem?_eq_getElem h]
  simp
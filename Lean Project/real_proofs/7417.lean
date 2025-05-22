import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat


example {l : List α} (h : l.drop n ≠ []) :
    (l.drop n).getLast h = l.getLast (ne_nil_of_length_pos (by simp at h; omega)) := by
  simp only [ne_eq, drop_eq_nil_iff_le] at h
  apply Option.some_inj.1
  simp only [← getLast?_eq_getLast, getLast?_drop, ite_eq_right_iff]
  omega
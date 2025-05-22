import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (l : List α) (i : Nat) (h : i < l.enum.length) :
    l.enum[i] = (i, l[i]'(by simpa [enum_length] using h)) := by
  simp [enum, nth, List.enumFrom, take]
  induction l generalizing i with
  | nil => simp
  | cons hd tl ih =>
    simp
    split_ifs with h
    . simp at h
      apply ih h
    . simp [List.get?]
      apply Nat.lt_succ_of_lt h

/- ACTUAL PROOF OF List.getElem_enum -/

example (l : List α) (i : Nat) (h : i < l.enum.length) :
    l.enum[i] = (i, l[i]'(by simpa [enum_length] using h)) := by
  simp [enum]
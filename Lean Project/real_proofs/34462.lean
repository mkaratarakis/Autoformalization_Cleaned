import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example {l : List α} {n m : Nat} (h : m < n) : (l.take n)[m]? = l[m]? := by
  induction n generalizing l m with
  | zero =>
    exact absurd h (Nat.not_lt_of_le m.zero_le)
  | succ _ hn =>
    cases l with
    | nil => simp only [take_nil]
    | cons hd tl =>
      cases m
      · simp
      · simpa using hn (Nat.lt_of_succ_lt_succ h)
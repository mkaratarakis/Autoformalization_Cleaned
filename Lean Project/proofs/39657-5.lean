import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (h : 0 < n) : find? p (replicate n a) = if p a then some a else none := by
  unfold replicate
  unfold find?
  cases n with
  | zero =>
    exfalso
    exact Nat.not_lt_zero 0 h
  | succ n' =>
    cases p a with
    | true =>
      rfl
    | false =>
      rfl

/- ACTUAL PROOF OF List.find?_replicate_of_length_pos -/

example (h : 0 < n) : find? p (replicate n a) = if p a then some a else none := by
  simp [find?_replicate, Nat.ne_of_gt h]
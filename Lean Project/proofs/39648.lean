import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (h : ¬ p a) : find? p (replicate n a) = none := by
  unfold find?
  cases n with
  | zero =>
    simp [replicate]
  | succ k =>
    simp [replicate]
    cases hp : p a with
    | false =>
      simp [hp]
    | true =>
      contradiction

/- ACTUAL PROOF OF List.find?_replicate_of_neg -/

example (h : ¬ p a) : find? p (replicate n a) = none := by
  simp [find?_replicate, h]
import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {p : α → Bool} {a : α} {l : List α} (h : p a) :
    (a :: l).takeWhile p = a :: l.takeWhile p := by
  unfold takeWhile
  simp [h]
  cases l with
  | nil => rfl
  | cons hd tl =>
    cases h : p hd with
    | true =>
      simp [h]
      apply congrArg2 _cons
      exact takeWhile_cons _ _ _
    | false =>
      simp [h]
      apply congrArg2 _cons
      exact takeWhile_nil _

/- ACTUAL PROOF OF List.takeWhile_cons_of_pos -/

example {p : α → Bool} {a : α} {l : List α} (h : p a) :
    (a :: l).takeWhile p = a :: l.takeWhile p := by
  simp [takeWhile_cons, h]
import Init.Data.Char.Basic
import Init.Data.UInt.Lemmas
import Init.Data.Char.Lemmas

open Char


example (a : Char) : ¬ a < a := by
  show left_not_iff.2 right_irrefl
  apply not_lt.2
  apply lt_irrefl

example (a : Char) : ¬ a < a := by
  show left_not_iff.2 right_irrefl
  apply not_lt.2
  apply lt_irrefl

/- ACTUAL PROOF OF Char.lt_irrefl -/

example (a : Char) : ¬ a < a := by
  simp
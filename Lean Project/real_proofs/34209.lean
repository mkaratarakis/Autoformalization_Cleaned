import Init.Data.Char.Basic
import Init.Data.UInt.Lemmas
import Init.Data.Char.Lemmas

open Char



example (a : Char) : ¬ a < a := by
  simp
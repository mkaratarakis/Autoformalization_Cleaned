import Init.Data.Char.Basic
import Init.Data.UInt.Lemmas
import Init.Data.Char.Lemmas

open Char


example (a : Char) : ¬ a < a := by
  rw [lt_irrefl]
  exact UInt32.not_le

example (a : Char) : ¬ a < a := by
  rw [lt_irrefl]
  exact UInt32.not_lt

example (a : Char) : a ≤ a := by
  rw [lt_irrefl]
  exact UInt32.le_refl

/- ACTUAL PROOF OF Char.lt_irrefl -/

example (a : Char) : ¬ a < a := by
  simp
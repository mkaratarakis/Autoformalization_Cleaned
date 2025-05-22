import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (!!b) = b := by
  cases b
  · calc
      !!false
        = !true := by simp
      _ = false := rfl

  · calc
      !!true
        = !false := by simp
      _ = true := rfl

/- ACTUAL PROOF OF Bool.not_not -/

example (b : Bool) : (!!b) = b := by
  cases b <;> rfl
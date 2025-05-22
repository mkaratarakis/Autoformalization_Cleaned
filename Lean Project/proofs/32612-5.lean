import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (!!b) = b := by
  cases b
  · calc
      !!false
        = !true := by simp only [not_false_eq_true]
      _ = false := rfl

  · calc
      !!true
        = !false := by simp only [not_true_eq_false]
      _ = true := rfl

/- ACTUAL PROOF OF Bool.not_not -/

example (b : Bool) : (!!b) = b := by
  cases b <;> rfl
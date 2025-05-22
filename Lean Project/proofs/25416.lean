import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(c t : Bool), cond c t false = ( c && t) := by
  intros c t
  cases c
  · -- Case where c is false
    cases t
    · -- t is false
      rfl
    · -- t is true
      rfl
  · -- Case where c is true
    cases t
    · -- t is false
      rfl
    · -- t is true
      rfl

/- ACTUAL PROOF OF Bool.cond_false_right -/

example : ∀(c t : Bool), cond c t false = ( c && t) := by
  decide
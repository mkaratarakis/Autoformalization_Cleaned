import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(b : Bool), (b = (!b)) ↔ False := by
  intro b
  cases b
  . -- case for true
    simp
    exact iff_false_intro (by simp)
  . -- case for false
    simp
    exact iff_false_intro (by simp)

/- ACTUAL PROOF OF Bool.eq_not_self -/

example : ∀(b : Bool), (b = (!b)) ↔ False := by
  decide
import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by
  intros a b
  cases a <;> cases b
  all_goals
    repeat (first | apply Bool.noConfusion)
  . case false.false => exact Iff.intro (by rfl) (by rfl)
  . case false.true => exact Iff.intro (fun h => by cases h) (fun h => by cases h)
  . case true.false => exact Iff.intro (fun h => by cases h) (fun h => by cases h)
  . case true.true => exact Iff.intro (by rfl) (by rfl)

/- ACTUAL PROOF OF Bool.not_eq_not -/

example : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by
  decide
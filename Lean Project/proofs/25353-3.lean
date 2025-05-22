import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by
  intros a b
  cases a <;> cases b
  all_goals
    repeat (first | apply Bool.noConfusion)
  . case false.false => rfl
  . case false.true => exact Iff.intro (fun h => False.elim (Bool.noConfusion h)) (fun h => False.elim (Bool.noConfusion h))
  . case true.false => exact Iff.intro (fun h => False.elim (Bool.noConfusion h)) (fun h => False.elim (Bool.noConfusion h))
  . case true.true => rfl

/- ACTUAL PROOF OF Bool.not_eq_not -/

example : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by
  decide
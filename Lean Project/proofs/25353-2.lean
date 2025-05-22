import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by
  intros a b
  cases a <;> cases b
  all_goals
    repeat (first | apply Bool.noConfusion)
  . case tt.tt => rfl
  . case ff.ff => rfl
  . case tt.ff => exact Iff.intro (fun h => False.elim (Bool.noConfusion h)) (fun h => False.elim (Bool.noConfusion h))
  . case ff.tt => exact Iff.intro (fun h => False.elim (Bool.noConfusion h)) (fun h => False.elim (Bool.noConfusion h))

/- ACTUAL PROOF OF Bool.not_eq_not -/

example : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by
  decide
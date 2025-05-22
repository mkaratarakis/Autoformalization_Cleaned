import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (t : Bool) :
    (ite p t false) = (p && t) := by
  by_cases hp : p
  · calc
      ite p t false = ite true t false := by rw [hp]
      _ = t := by rw [if_pos]
      _ = t && true := by simp
      _ = t && decide p := by simp [hp, decide_eq_true_iff]

  · calc
      ite p t false = ite false t false := by rw [hp]
      _ = false := by rw [if_neg]
      _ = false && t := by simp
      _ = decide p && t := by simp [hp, decide_eq_false_iff]

/- ACTUAL PROOF OF Bool.if_false_right -/

example (p : Prop) [h : Decidable p] (t : Bool) :
    (ite p t false) = (p && t) := by
  cases h with | _ p => simp [p]
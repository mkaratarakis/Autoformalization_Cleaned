import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (t : Bool) :
    (ite p t false) = (p && t) := by
  by_cases hp : p
  · calc
      ite p t false = ite true t false := by rw [hp]
      _ = t := by rw [if_pos]
      _ = true && t := by rw [decide_eq_true_iff]
      _ = (decide p) && t := by rw [hp]

  · calc
      ite p t false = ite false t false := by rw [hp]
      _ = false := by rw [if_neg]
      _ = false && t := by rw [decide_eq_false_iff]
      _ = (decide p) && t := by rw [hp]

/- ACTUAL PROOF OF Bool.if_false_right -/

example (p : Prop) [h : Decidable p] (t : Bool) :
    (ite p t false) = (p && t) := by
  cases h with | _ p => simp [p]
import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (t : Bool) :
    (ite p t false) = (p && t) := by
  by_cases hp : p
  · have hdec : decide p = true
    {
      change decide p = true,
      apply Decidable.decide_true,
      exact hp,
    }
    calc
      ite p t false = ite true t false := by rw [hp]
      ... = t := by rw [if_pos]
      ... = true && t := by rw [hdec]
      ... = p && t := by rw [hp]

  · have hdecf : decide p = false
    {
      change decide p = false,
      apply Decidable.decide_false,
      exact hp,
    }
    calc
      ite p t false = ite false t false := by rw [hp]
      ... = false := by rw [if_neg]
      ... = false && t := by rw [hdecf]
      ... = p && t := by rw [hp]

/- ACTUAL PROOF OF Bool.if_false_right -/

example (p : Prop) [h : Decidable p] (t : Bool) :
    (ite p t false) = (p && t) := by
  cases h with | _ p => simp [p]
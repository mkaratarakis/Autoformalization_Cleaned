import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p q : Prop) [dpq : Decidable (p ↔ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ↔ q) = (decide p == decide q) := by
  by_cases hp : p
  · -- Case 1: p is true
    have h1 : decide p = true := by exact if_pos hp
    have h2 : decide (p ↔ q) = decide q := by
      change decide (p ↔ q) = decide q
      rw [decide_eq_true_iff]
      apply propext
      apply Iff.intro
      · intro h
        exact iff_of_true hp h
      · intro h
        exact iff_of_true hp h
    rw [h1, h2]
    rfl
  · -- Case 2: p is false
    have h1 : decide p = false := by exact if_neg hp
    have h2 : decide (p ↔ q) = !decide q := by
      change decide (p ↔ q) = !decide q
      rw [decide_eq_false_iff]
      apply propext
      apply Iff.intro
      · intro h
        exact iff_of_false h
      · intro h
        exact iff_of_false h
    rw [h1, h2]
    rfl

/- ACTUAL PROOF OF Bool.decide_iff_dist -/

example (p q : Prop) [dpq : Decidable (p ↔ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ↔ q) = (decide p == decide q) := by
  cases dp with | _ p => simp [p]
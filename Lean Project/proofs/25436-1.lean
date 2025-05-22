import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p q : Prop) [dpq : Decidable (p ↔ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ↔ q) = (decide p == decide q) := by
  by_cases hp : p
  · -- Case 1: p is true
    have h1 : decide p = true := by exact if_pos hp
    have h2 : decide (p ↔ q) = decide q := by
      apply propext
      · intro hpq
        exact iff_of_true hp hpq
      · intro hq
        exact iff_of_true hp (iff_of_true hp hq).elim
    rw [h1, h2]
    exact eq_true_intro (decide q)
  · -- Case 2: p is false
    have h1 : decide p = false := by exact if_neg hp
    have h2 : decide (p ↔ q) = bnot (decide q) := by
      apply propext
      · intro hpq
        exact iff_of_false (iff_of_false hp hpq)
      · intro hq
        exact iff_of_false (iff_of_false hp (iff_of_false hp hq).elim)
    rw [h1, h2]
    exact eq_false_intro (bnot (decide q))

/- ACTUAL PROOF OF Bool.decide_iff_dist -/

example (p q : Prop) [dpq : Decidable (p ↔ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ↔ q) = (decide p == decide q) := by
  cases dp with | _ p => simp [p]
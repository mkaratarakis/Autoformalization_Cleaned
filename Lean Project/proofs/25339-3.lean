import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (b : Bool) : (true = b) = (b = true) := by
  cases b with
  | false =>
    apply Eq.symm
    apply Eq.symm
    apply Eq.symm
    exact (false_ne_true _).symm
  | true =>
    rfl

/- ACTUAL PROOF OF Bool.true_eq -/

example (b : Bool) : (true = b) = (b = true) := by
  cases b <;> simp
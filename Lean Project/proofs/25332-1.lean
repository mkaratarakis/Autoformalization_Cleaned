import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y : Bool), (x && y) = false ↔ (x = true → y = false) := by
  intros x y
  cases x
  · -- Case where x = false
    simp [and_false]
    intros h
    apply False.elim
    apply h
    exact Bool.noConfusion rfl
  · -- Case where x = true
    cases y
    · -- Subcase where y = false
      simp [true_and]
      exact Iff.rfl
    · -- Subcase where y = true
      simp [true_and]
      intro h
      apply False.elim
      exact h rfl

/- ACTUAL PROOF OF Bool.and_eq_false_imp -/

example : ∀ (x y : Bool), (x && y) = false ↔ (x = true → y = false) := by
  decide
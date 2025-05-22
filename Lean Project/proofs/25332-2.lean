import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y : Bool), (x && y) = false ↔ (x = true → y = false) := by
  intros x y
  cases x
  · -- Case where x = false
    simp
    constructor
    · intro h
      exact h.elim
    · intro h
      exact h.elim
  · -- Case where x = true
    cases y
    · -- Subcase where y = false
      simp
      exact Iff.rfl
    · -- Subcase where y = true
      simp
      constructor
      · intro h
        apply False.elim
        exact h rfl
      · intro h
        apply False.elim
        exact h rfl

/- ACTUAL PROOF OF Bool.and_eq_false_imp -/

example : ∀ (x y : Bool), (x && y) = false ↔ (x = true → y = false) := by
  decide
import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a = (a && b)) ↔ (a → b) := by
  intro a b
  by_cases h : a = true
  · simp [h]
    exact Iff.intro
      (fun h1 => by
        simp [h1])
      (fun h1 => by
        simp [h1]
        exact h)
  · simp [h]
    apply Iff.intro
    · intro h1
      exact (h rfl).elim
    · intro h1
      exfalso
      exact h rfl

/- ACTUAL PROOF OF Bool.iff_self_and -/

example : ∀(a b : Bool), (a = (a && b)) ↔ (a → b) := by
  decide
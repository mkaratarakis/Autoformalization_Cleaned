import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a = (a && b)) ↔ (a → b) := by
  intro a b
  by_cases h : a = true
  · simp [h]
    exact Iff.intro
        (fun h1 => by simp [h1])
        (fun h1 => by
          simp [h1]
          exact h)
  · simp [h]
    exact Iff.intro
        (by
          simp [h])
        (by
          rintro rfl
          exact h)

/- ACTUAL PROOF OF Bool.iff_self_and -/

example : ∀(a b : Bool), (a = (a && b)) ↔ (a → b) := by
  decide
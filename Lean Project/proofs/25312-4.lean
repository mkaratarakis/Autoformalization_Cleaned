import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), ((a && b) = b) ↔ (b → a) := by
  intros a b
  apply Iff.intro
  . intro h
    cases b
    . simp at h
      exact h
    . simp at h
      exact fun hb => (False.elim (hb rfl))
  . intro h
    cases b
    . simp
      intro hb
      exact h hb
    . simp

/- ACTUAL PROOF OF Bool.and_iff_right_iff_imp -/

example : ∀(a b : Bool), ((a && b) = b) ↔ (b → a) := by
  decide
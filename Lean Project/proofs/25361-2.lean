import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a ↔ b) ↔ a = b := by
  intro a b
  apply Iff.intro
  . intro h
    cases a <;> cases b <;> simp [*] at *
    . simp
    . simp at h
    . simp at h
    . simp
  . intro h
    exact h

/- ACTUAL PROOF OF Bool.coe_iff_coe -/

example : ∀(a b : Bool), (a ↔ b) ↔ a = b := by
  decide
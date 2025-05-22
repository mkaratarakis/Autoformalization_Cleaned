import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a ↔ b) ↔ a = b := by
  intro a b
  apply Iff.intro
  . intro h
    cases a <;> cases b <;> simp [*] at *
    . simp
      exact h.mp
    . simp at h
      exact h.mpr
    . simp at h
      exact h.mpr
    . simp
      exact h.mp
  . intro h
    cases h
    . cases a <;> cases b <;> simp [*] at *
      . simp
      . simp at h
      . simp at h
      . simp
    . cases a <;> cases b <;> simp [*] at *
      . simp
      . simp at h
      . simp at h
      . simp

/- ACTUAL PROOF OF Bool.coe_iff_coe -/

example : ∀(a b : Bool), (a ↔ b) ↔ a = b := by
  decide
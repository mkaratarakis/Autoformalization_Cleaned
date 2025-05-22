import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a ↔ b) ↔ a = b := by
  intro a b
  apply Iff.intro
  . intro h
    cases a <;> cases b <;> simp [*] at *
    . exact Iff.rfl
    . exact Iff.rfl
    . exact Iff.rfl
    . exact Iff.rfl
  . intro h
    cases a <;> cases b <;> simp [*] at *
    . exact Iff.rfl
    . exact Iff.rfl
    . exact Iff.rfl
    . exact Iff.rfl

/- ACTUAL PROOF OF Bool.coe_iff_coe -/

example : ∀(a b : Bool), (a ↔ b) ↔ a = b := by
  decide
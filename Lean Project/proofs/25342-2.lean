import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a = false ↔ b) ↔ (!a) = b := by
  intro a b
  apply Iff.intro
  . intro h
    cases a <;> simp [h]
    . exact h.mpr rfl
    . exact h.mp rfl
  . intro h
    cases a <;> simp [h]
    . exact Iff.intro (fun hb => h.symm ∘ congrArg not hb) (fun hb => h.trans (congrArg not hb))
    . exact Iff.intro (fun hb => h.symm ∘ congrArg not hb) (fun hb => h.trans (congrArg not hb))

/- ACTUAL PROOF OF Bool.coe_false_iff_true -/

example : ∀(a b : Bool), (a = false ↔ b) ↔ (!a) = b := by
  decide
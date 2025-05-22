import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a = false ↔ b) ↔ (!a) = b := by
  intro a b
  apply Iff.intro
  . intro h
    cases a <;> simp [h]
    . apply h.mp
      refl
    . apply h.mpr
      apply True.intro
  . intro h
    cases a <;> simp [h]
    . exact Iff.intro (fun _ => rfl) (fun _ => rfl)
    . exact Iff.intro (fun _ => rfl) (fun _ => rfl)

/- ACTUAL PROOF OF Bool.coe_false_iff_true -/

example : ∀(a b : Bool), (a = false ↔ b) ↔ (!a) = b := by
  decide
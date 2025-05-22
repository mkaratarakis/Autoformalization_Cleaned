import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a = false ↔ b) ↔ (!a) = b := by
  intro a b
  apply Iff.intro
  . intro h
    cases a <;> simp [h]
    . exact h.2
    . exact h.1
  . intro h
    cases a <;> simp [h]
    . exact Iff.intro (fun hb => by simp [h, hb]) (fun hb => by simp [h, hb])
    . exact Iff.intro (fun hb => by simp [h, hb]) (fun hb => by simp [h, hb])

/- ACTUAL PROOF OF Bool.coe_false_iff_true -/

example : ∀(a b : Bool), (a = false ↔ b) ↔ (!a) = b := by
  decide
import Init.SizeOf
import Init.Data.Nat.Basic
import Init.WF

open Subrelation
variable {α : Sort u} {r : α → α → Prop}
variable {α : Sort u} {r : α → α → Prop} (hwf : WellFounded r)
variable {C : α → Sort v}
variable (F : ∀ x, (∀ y, r y x → C y) → C x)
variable (F : ∀ x, (∀ y, r y x → C y) → C x)
variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}
open WellFounded
variable {α : Sort u} {r q : α → α → Prop}

example {a : α} (h₁ : Subrelation q r) (ac : Acc r a) : Acc q a := by
  apply Acc.recOn ac
  clear ac
  intro x ih
  exact Acc.intro _ fun y hyx => ih y (h₁ hyx)

/- ACTUAL PROOF OF Subrelation.accessible -/

example {a : α} (h₁ : Subrelation q r) (ac : Acc r a) : Acc q a := by
  induction ac with
  | intro x _ ih =>
    apply Acc.intro
    intro y h
    exact ih y (h₁ h)
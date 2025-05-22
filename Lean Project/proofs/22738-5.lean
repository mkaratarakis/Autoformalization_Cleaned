import Init.SizeOf
import Init.Data.Nat.Basic
import Init.WF

open Prod
variable {α : Sort u} {r : α → α → Prop}
variable {α : Sort u} {r : α → α → Prop} (hwf : WellFounded r)
variable {C : α → Sort v}
variable (F : ∀ x, (∀ y, r y x → C y) → C x)
variable (F : ∀ x, (∀ y, r y x → C y) → C x)
variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}
open WellFounded
variable {α : Sort u} {r q : α → α → Prop}
variable {α : Sort u} {β : Sort v} {r : β → β → Prop}
open Relation
open WellFounded
variable {α : Type u} {β : Type v}
variable  (ra  : α → α → Prop)
variable  (rb  : β → β → Prop)
variable  (ra  : α → α → Prop)
variable  (rb  : β → β → Prop)
variable  (rb  : β → β → Prop)
variable {α : Type u} {β : Type v}
variable {ra  : α → α → Prop} {rb  : β → β → Prop}
variable {ra  : α → α → Prop} {rb  : β → β → Prop}

example (a : α × β) (b : α × β) (h : RProd ra rb a b) : Prod.Lex ra rb a b := by
  rcases a with ⟨a1, b1⟩
  rcases b with ⟨a2, b2⟩
  apply Prod.Lex.left
  apply And.left
  exact h

/- ACTUAL PROOF OF Prod.RProdSubLex -/

example (a : α × β) (b : α × β) (h : RProd ra rb a b) : Prod.Lex ra rb a b := by
  cases h with
  | intro h₁ h₂ => exact Prod.Lex.left _ _ h₁
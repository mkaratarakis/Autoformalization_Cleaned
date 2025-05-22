import Init.SizeOf
import Init.Data.Nat.Basic
import Init.WF

open PSigma
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
variable {α : Sort u} {β : α → Sort v}
variable  (r  : α → α → Prop)
variable  (s  : ∀ a, β a → β a → Prop)
variable  (r  : α → α → Prop)
variable  (s  : ∀ a, β a → β a → Prop)
variable  (s  : ∀ a, β a → β a → Prop)
variable {α : Sort u} {β : α → Sort v}
variable {r  : α → α → Prop} {s : ∀ (a : α), β a → β a → Prop}
variable {r  : α → α → Prop} {s : ∀ (a : α), β a → β a → Prop}

example {a} (aca : Acc r a) (acb : (a : α) → WellFounded (s a)) (b : β a) : Acc (Lex r s) ⟨a, b⟩ := by
  induction aca with
  | intro xa iha =>
    exact (acb xa).recOnAcc (fun xb ihb =>
      Acc.intro ⟨xa, xb⟩ (by
        intro p
        intro lt
        rcases p with ⟨ y, z ⟩
        rcases lt with (r_lt | ⟨ hr, hs ⟩)
        · exact iha y z r_lt
        · exact ihb y z hs

/- ACTUAL PROOF OF PSigma.lexAccessible -/

example {a} (aca : Acc r a) (acb : (a : α) → WellFounded (s a)) (b : β a) : Acc (Lex r s) ⟨a, b⟩ := by
  induction aca with
  | intro xa _ iha =>
    induction (WellFounded.apply (acb xa) b) with
    | intro xb _ ihb =>
      apply Acc.intro
      intro p lt
      cases lt with
      | left  => apply iha; assumption
      | right => apply ihb; assumption
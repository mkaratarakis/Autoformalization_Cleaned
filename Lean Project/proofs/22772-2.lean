import Init.SizeOf
import Init.Data.Nat.Basic
import Init.WF

open Acc
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

example (h : Acc r a) : Acc (TransGen r) a := by
  apply Acc.intro
  intros x hx
  apply Acc.intro
  intros y hy
  cases' h_1 : (TransGen r) y x with
  | base y x r_yx =>
    apply h
    exact r_yx
  | step y x z hz_1 hz_2 =>
    apply hx z hz_2
    apply hz_1

/- ACTUAL PROOF OF Acc.transGen -/

example (h : Acc r a) : Acc (TransGen r) a := by
  induction h with
  | intro x _ H =>
    refine Acc.intro x fun y hy ↦ ?_
    cases hy with
    | single hyx =>
      exact H y hyx
    | tail hyz hzx =>
      exact (H _ hzx).inv hyz
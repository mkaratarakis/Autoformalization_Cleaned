import Mathlib.Order.Antichain
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Minimal

open Minimal
open Set OrderDual
variable {α : Type*} {P Q : α → Prop} {a x y : α}
variable [LE α]

example (h : Minimal (fun x ↦ P x ∨ Q x) x) : Minimal P x ∨ Minimal Q x := by
  cases h
  case inl hPQ =>
    apply Or.inl
    intros y hx hy
    apply hPQ
    left
    exact ⟨hy, hx⟩
  case inr hPQ =>
    apply Or.inr
    intros y hx hy
    apply hPQ
    right
    exact ⟨hy, hx⟩
  intros y hy
  simp at hy
  cases hy
  case inl hyP =>
    apply Or.inl
    intros z hxz hzx
    apply hPQ
    left
    exact ⟨hxz, hzx⟩
  case inr hyQ =>
    apply Or.inr
    intros z hxz hzx
    apply hPQ
    right
    exact ⟨hxz, hzx⟩

/- ACTUAL PROOF OF Minimal.or -/

example (h : Minimal (fun x ↦ P x ∨ Q x) x) : Minimal P x ∨ Minimal Q x := by
  obtain ⟨h | h, hmin⟩ := h
  · exact .inl ⟨h, fun y hy hyx ↦ hmin (Or.inl hy) hyx⟩
  exact .inr ⟨h, fun y hy hyx ↦ hmin (Or.inr hy) hyx⟩
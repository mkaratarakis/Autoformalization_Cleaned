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
  · intro y hy hyx
    simp at hy
    cases hy
    · apply Or.inl
      intros z hxz hzx
      apply h_left
      exact ⟨hxz, hzx⟩
    · apply Or.inr
      intros z hxz hzx
      apply h_left
      exact ⟨hxz, hzx⟩
  · intro y hy hyx
    simp at hy
    cases hy
    · apply Or.inl
      intros z hxz hzx
      apply h_right
      exact ⟨hxz, hzx⟩
    · apply Or.inr
      intros z hxz hzx
      apply h_right
      exact ⟨hxz, hzx⟩

/- ACTUAL PROOF OF Minimal.or -/

example (h : Minimal (fun x ↦ P x ∨ Q x) x) : Minimal P x ∨ Minimal Q x := by
  obtain ⟨h | h, hmin⟩ := h
  · exact .inl ⟨h, fun y hy hyx ↦ hmin (Or.inl hy) hyx⟩
  exact .inr ⟨h, fun y hy hyx ↦ hmin (Or.inr hy) hyx⟩
import Mathlib.Order.Antichain
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Minimal

open Minimal
open Set OrderDual
variable {α : Type*} {P Q : α → Prop} {a x y : α}
variable [LE α]

example (h : Minimal (fun x ↦ P x ∨ Q x) x) : Minimal P x ∨ Minimal Q x := by
  by_cases hPx : P x
  · left
    refine' ⟨hPx, _⟩
    rintro y hyPQ hle
    exact h hle (Or.inl hyPQ)
  · right
    refine' ⟨hPx, _⟩
    rintro y hyPQ hle
    exact h hle (Or.inr hyPQ)

/- ACTUAL PROOF OF Minimal.or -/

example (h : Minimal (fun x ↦ P x ∨ Q x) x) : Minimal P x ∨ Minimal Q x := by
  obtain ⟨h | h, hmin⟩ := h
  · exact .inl ⟨h, fun y hy hyx ↦ hmin (Or.inl hy) hyx⟩
  exact .inr ⟨h, fun y hy hyx ↦ hmin (Or.inr hy) hyx⟩
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
    constructor
    · intros y hPy hle
      exact h hle hPy (Or.inl hPy)
    · exact hPx
  · right
    constructor
    · intros y hQy hle
      exact h hle hQy (Or.inr hQy)
    · exact hPx

/- ACTUAL PROOF OF Minimal.or -/

example (h : Minimal (fun x ↦ P x ∨ Q x) x) : Minimal P x ∨ Minimal Q x := by
  obtain ⟨h | h, hmin⟩ := h
  · exact .inl ⟨h, fun y hy hyx ↦ hmin (Or.inl hy) hyx⟩
  exact .inr ⟨h, fun y hy hyx ↦ hmin (Or.inr hy) hyx⟩
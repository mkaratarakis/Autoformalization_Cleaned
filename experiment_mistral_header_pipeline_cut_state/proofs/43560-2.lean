import Mathlib.Data.Option.Basic
import Mathlib.Data.Set.Basic
import Batteries.Tactic.Congr
import Mathlib.Data.PEquiv

open PEquiv
variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
open Function Option

example (f : α ≃. β) {a₁ a₂ : α} {b : β} (h₁ : b ∈ f a₁) (h₂ : b ∈ f a₂) :
    a₁ = a₂ := by
  have h₁' : a₁ ∈ invFun f b := by
    rw [← mem_map_of_injective (Option.some.inj)] at h₁
    exact h₁
  have h₂' : a₂ ∈ invFun f b := by
    rw [← mem_map_of_injective (Option.some.inj)] at h₂
    exact h₂
  rw [← inv f a₁ b, h₁']
  rw [← inv f a₂ b, h₂']
  exact h₁'

/- ACTUAL PROOF OF PEquiv.inj -/

example (f : α ≃. β) {a₁ a₂ : α} {b : β} (h₁ : b ∈ f a₁) (h₂ : b ∈ f a₂) :
    a₁ = a₂ := by
  rw [← mem_iff_mem] at *; cases h : f.symm b <;> simp_all
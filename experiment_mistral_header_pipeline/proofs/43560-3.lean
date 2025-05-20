import Mathlib.Data.Option.Basic
import Mathlib.Data.Set.Basic
import Batteries.Tactic.Congr
import Mathlib.Data.PEquiv

open PEquiv
variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
open Function Option

example (f : α ≃. β) {a₁ a₂ : α} {b : β} (h₁ : b ∈ f a₁) (h₂ : b ∈ f a₂) :
    a₁ = a₂ := by
  have hinv₁ : b ∈ f a₁ := h₁
  have hinv₂ : b ∈ f a₂ := h₂
  rw [Option.eq_of_mem_of_mem hinv₁ hinv₂]

/- ACTUAL PROOF OF PEquiv.inj -/

example (f : α ≃. β) {a₁ a₂ : α} {b : β} (h₁ : b ∈ f a₁) (h₂ : b ∈ f a₂) :
    a₁ = a₂ := by
  rw [← mem_iff_mem] at *; cases h : f.symm b <;> simp_all
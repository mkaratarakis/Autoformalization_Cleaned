import Mathlib.Data.Option.Basic
import Mathlib.Data.Set.Basic
import Batteries.Tactic.Congr
import Mathlib.Data.PEquiv

open PEquiv
variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
open Function Option

example (f : α ≃. β) {a₁ a₂ : α} {b : β} (h₁ : b ∈ f a₁) (h₂ : b ∈ f a₂) :
    a₁ = a₂ := by
  have h₁' : a₁ ∈ f.symm b := by
    simpa only [mem_symm_iff] using h₁
  have h₂' : a₂ ∈ f.symm b := by
    simpa only [mem_symm_iff] using h₂
  exact (Set.eq_of_mem_singleton h₁').symm.trans (Set.eq_of_mem_singleton h₂')
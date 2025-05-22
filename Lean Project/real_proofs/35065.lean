import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]


example {a : α} {l l'} :
    a :: l <+ l' ↔ ∃ r₁ r₂, l' = r₁ ++ r₂ ∧ a ∈ r₁ ∧ l <+ r₂ := by
  induction l' with
  | nil => simp
  | cons a' l' ih =>
    constructor
    · intro w
      cases w with
      | cons _ w =>
        obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := ih.1 w
        exact ⟨a' :: r₁, r₂, by simp, mem_cons_of_mem a' h₁, h₂⟩
      | cons₂ _ w =>
        exact ⟨[a], l', by simp, mem_singleton_self _, w⟩
    · rintro ⟨r₁, r₂, w, h₁, h₂⟩
      rw [w, ← singleton_append]
      exact Sublist.append (by simpa) h₂
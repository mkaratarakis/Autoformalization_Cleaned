import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isPrefixOf l₂ ↔ l₁ <+: l₂ := by
  induction l₁ with
  | nil =>
    simp [isPrefixOf]
    exact Iff.intro (fun _ => List.Prefix.refl) (fun _ => true)
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      simp [isPrefixOf]
      exact Iff.intro (fun h => False.elim (List.not_mem_nil a h)) (fun h => False.elim h)
    | cons a' l₂ =>
      simp [isPrefixOf]
      split
      · intro h
        cases h
        case inl h => exact False.elim (h (ne_of_mem_of_not_mem (Or.inr ⟨a, a', l₂, rfl⟩) (mt (· ≠ ·) h)))
        case inr h => exact ih.mp h
      · intro h
        cases h
        case inl h => exact Or.inl (Eq.ndrec (fun a' => a = a' → List.isPrefixOf l₁ l₂) h)
        case inr h => exact Or.inr (ih.mpr h)

/- ACTUAL PROOF OF List.isPrefixOf_iff_prefix -/

example [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isPrefixOf l₂ ↔ l₁ <+: l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons a' l₂ => simp [isPrefixOf, ih]
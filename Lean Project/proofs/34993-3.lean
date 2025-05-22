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
    exact Iff.intro (fun _ => List.Prefix.refl) (fun _ => true.intro)
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
        case inl h =>
          rw [h]
          exact List.Prefix.refl
        case inr h =>
          apply List.Prefix.cons
          · exact h
          · apply ih.mp
          exact h
      · intro h
        cases h
        case refl =>
          exact Or.inl rfl
        case cons hp hs =>
          exact Or.inr (ih.mpr hs)

/- ACTUAL PROOF OF List.isPrefixOf_iff_prefix -/

example [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isPrefixOf l₂ ↔ l₁ <+: l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons a' l₂ => simp [isPrefixOf, ih]
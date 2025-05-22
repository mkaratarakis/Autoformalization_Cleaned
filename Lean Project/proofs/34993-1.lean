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
    simp [isPrefixOf, List.Prefix]
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      simp [isPrefixOf, List.Prefix]
    | cons a' l₂ =>
      simp [isPrefixOf, List.Prefix]
      split
      · intro h
        exact And.intro (congrArg Prod.fst h) (ih.mp (congrArg Prod.snd h))
      · rintro ⟨rfl, h⟩
        exact And.intro rfl (ih.mpr h)

/- ACTUAL PROOF OF List.isPrefixOf_iff_prefix -/

example [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isPrefixOf l₂ ↔ l₁ <+: l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons a' l₂ => simp [isPrefixOf, ih]
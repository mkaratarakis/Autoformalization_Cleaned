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
    exact Iff.intro (fun _ => List.Prefix.refl) (fun _ => trivial)
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      simp [isPrefixOf]
      exact Iff.intro (fun h => False.elim (List.not_mem_nil a h)) (fun h => False.elim h)
    | cons a' l₂ =>
      simp [isPrefixOf]
      by_cases h : a = a'
      · rw [h]
        exact Iff.intro ih.mp ih.mpr
      · simp [h]
        exact Iff.intro (fun h => False.elim (List.not_mem_nil a h)) (fun h => False.elim h)

/- ACTUAL PROOF OF List.isPrefixOf_iff_prefix -/

example [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isPrefixOf l₂ ↔ l₁ <+: l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons a' l₂ => simp [isPrefixOf, ih]
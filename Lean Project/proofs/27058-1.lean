import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldr g i = (zip l₁ l₂).foldr (fun p r => g (f p.1 p.2) r) i := by
  induction l₁ generalizing l₂
  case nil =>
    cases l₂
    case nil => simp
    case cons => simp
  case cons =>
    cases l₂
    case nil => simp
    case cons =>
      simp [ih]

/- ACTUAL PROOF OF List.zipWith_foldr_eq_zip_foldr -/

example {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldr g i = (zip l₁ l₂).foldr (fun p r => g (f p.1 p.2) r) i := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all
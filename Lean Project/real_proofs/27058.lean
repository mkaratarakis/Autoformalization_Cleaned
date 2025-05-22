import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldr g i = (zip l₁ l₂).foldr (fun p r => g (f p.1 p.2) r) i := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp_all
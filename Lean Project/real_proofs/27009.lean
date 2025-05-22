import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example {f : α → β → γ} (i : δ):
    (zipWith f l₁ l₂).foldl g i = (zip l₁ l₂).foldl (fun r p => g r (f p.1 p.2)) i := by
  induction l₁ generalizing i l₂ <;> cases l₂ <;> simp_all
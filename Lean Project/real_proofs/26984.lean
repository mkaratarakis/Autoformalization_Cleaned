import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example (f : α → γ) (l₁ : List α) (l₂ : List β) :
    zip (l₁.map f) l₂ = (zip l₁ l₂).map (Prod.map f id) := by
  rw [← zip_map, map_id]
import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example {f : α → β → γ} {l l'} : zipWith f l l' = [] ↔ l = [] ∨ l' = [] := by
  cases l <;> cases l' <;> simp
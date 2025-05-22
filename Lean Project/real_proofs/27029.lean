import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example {f : α → β → γ} {i : Nat} :
    (zipWith f l₁ l₂)[i]? = (l₁[i]?.map f).bind fun g => l₂[i]?.map g := by
  induction l₁ generalizing l₂ i with
  | nil => rw [zipWith] <;> simp
  | cons head tail =>
    cases l₂
    · simp
    · cases i <;> simp_all
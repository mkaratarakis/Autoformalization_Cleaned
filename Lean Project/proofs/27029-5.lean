import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {f : α → β → γ} {i : Nat} :
    (zipWith f l₁ l₂)[i]? = (l₁[i]?.map f).bind fun g => l₂[i]?.map g := by
  induction l₁ generalizing l₂ with
  | nil =>
    simp
  | cons head tail ih =>
    cases l₂ with
    | nil =>
      simp
    | cons head' tail' =>
      cases i with
      | zero =>
        simp
      | succ n =>
        simp [zipWith]
        rw [ih (tail' : List β)]
        simp

/- ACTUAL PROOF OF List.getElem?_zipWith' -/

example {f : α → β → γ} {i : Nat} :
    (zipWith f l₁ l₂)[i]? = (l₁[i]?.map f).bind fun g => l₂[i]?.map g := by
  induction l₁ generalizing l₂ i with
  | nil => rw [zipWith] <;> simp
  | cons head tail =>
    cases l₂
    · simp
    · cases i <;> simp_all
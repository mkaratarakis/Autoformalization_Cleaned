import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example (l₁ : List α) (l₂ : List β) (z : α × β) (i : Nat) :
    (zip l₁ l₂)[i]? = some z ↔ l₁[i]? = some z.1 ∧ l₂[i]? = some z.2 := by
  cases z
  rw [zip, getElem?_zipWith_eq_some]; constructor
  · rintro ⟨x, y, h₀, h₁, h₂⟩
    simpa [h₀, h₁] using h₂
  · rintro ⟨h₀, h₁⟩
    exact ⟨_, _, h₀, h₁, rfl⟩
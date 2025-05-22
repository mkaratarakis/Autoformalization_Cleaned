import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example (l₁ : List α) (l₂ : List β) (z : α × β) (i : Nat) :
    (zip l₁ l₂)[i]? = some z ↔ l₁[i]? = some z.1 ∧ l₂[i]? = some z.2 := by
  unfold zip
  simp
  constructor
  · intro h
    rcases h with ⟨x, y, hx, hy, hz⟩
    exact ⟨hx, hy⟩
  · intro h
    rcases h with ⟨hx, hy⟩
    exists z.1, z.2
    simp
    split
    · exact hx
    · exact hy
    · rfl

/- ACTUAL PROOF OF List.getElem?_zip_eq_some -/

example (l₁ : List α) (l₂ : List β) (z : α × β) (i : Nat) :
    (zip l₁ l₂)[i]? = some z ↔ l₁[i]? = some z.1 ∧ l₂[i]? = some z.2 := by
  cases z
  rw [zip, getElem?_zipWith_eq_some]; constructor
  · rintro ⟨x, y, h₀, h₁, h₂⟩
    simpa [h₀, h₁] using h₂
  · rintro ⟨h₀, h₁⟩
    exact ⟨_, _, h₀, h₁, rfl⟩
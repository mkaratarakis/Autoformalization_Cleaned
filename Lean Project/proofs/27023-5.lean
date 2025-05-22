import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {l₁ : List α} {l₂ : List β} (h : length l₁ = length l₂) :
    unzip (zip l₁ l₂) = (l₁, l₂) := by
  induction l₁ generalizing l₂
  · simp only [zip, unzip, nil_eq, Prod.mk.inj_iff, eq_self_iff_true, and_self_iff]
    exact ⟨rfl, rfl⟩
  · simp only [zip, unzip, cons_eq, Prod.mk.inj_iff, eq_self_iff_true, and_self_iff]
    exact ⟨rfl, rfl⟩

/- ACTUAL PROOF OF List.unzip_zip -/

example {l₁ : List α} {l₂ : List β} (h : length l₁ = length l₂) :
    unzip (zip l₁ l₂) = (l₁, l₂) := by
  ext
  · rw [unzip_zip_left (Nat.le_of_eq h)]
  · rw [unzip_zip_right (Nat.le_of_eq h.symm)]
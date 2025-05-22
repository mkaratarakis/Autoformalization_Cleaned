import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example (l₁ : List α) (l₂ : List β) :
    length (zip l₁ l₂) = min (length l₁) (length l₂) := by
  induction l₁ with
  | nil =>
    simp [zip]
  | cons x xs =>
    cases l₂ with
    | nil =>
      simp [zip]
    | cons y ys =>
      simp [zip, length, min]
      rw [ Nat.succ_min ]
      exact Nat.succ_inj.mpr (zip_length_eq_min xs ys)

/- ACTUAL PROOF OF List.length_zip -/

example (l₁ : List α) (l₂ : List β) :
    length (zip l₁ l₂) = min (length l₁) (length l₂) := by
  simp [zip]
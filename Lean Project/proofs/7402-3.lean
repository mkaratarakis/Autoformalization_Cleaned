import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {l₁ l₂ : List α} {n : Nat} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ := by
  have : n ≤ l₁.length + l₂.length := by
    exact Nat.le_add_right l₂.length h
  rw [drop_append]
  have : n - l₁.length = 0 := by
    exact Nat.sub_eq_zero_of_le h
  rw [this, drop_zero]
  rfl

/- ACTUAL PROOF OF List.drop_append_of_le_length -/

example {l₁ l₂ : List α} {n : Nat} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ := by
  simp [drop_append_eq_append_drop, Nat.sub_eq_zero_of_le h]
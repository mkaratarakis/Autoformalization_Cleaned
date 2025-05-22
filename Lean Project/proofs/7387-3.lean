import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {l₁ l₂ : List α} {n : Nat} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).take n = l₁.take n := by
  rw [take_append]
  have : n - l₁.length = 0 := by
    apply Nat.sub_eq_zero_of_le
    exact h
  rw [this]
  simp

/- ACTUAL PROOF OF List.take_append_of_le_length -/

example {l₁ l₂ : List α} {n : Nat} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).take n = l₁.take n := by
  simp [take_append_eq_append_take, Nat.sub_eq_zero_of_le h]
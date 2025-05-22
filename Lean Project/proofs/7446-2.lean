import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {a : α} {b : β} {m n : Nat} :
    zip (replicate m a) (replicate n b) = replicate (min m n) (a, b) := by
  cases min_cases m n with
  | inl h =>
    simp only [zip_nil_left, replicate_zero, Nat.min_eq_left h]
  | inr h =>
    simp only [zip_nil_right, replicate_zero, Nat.min_eq_right h]

/- ACTUAL PROOF OF List.zip_replicate -/

example {a : α} {b : β} {m n : Nat} :
    zip (replicate m a) (replicate n b) = replicate (min m n) (a, b) := by
  rw [zip_eq_zip_take_min]
  simp
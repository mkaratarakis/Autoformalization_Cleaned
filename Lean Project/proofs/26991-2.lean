import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example (f : α → α → β) (comm : ∀ x y : α, f x y = f y x) (l l' : List α) :
    zipWith f l l' = zipWith f l' l := by
  rw [zipWith_comm]
  apply congr_fun
  apply congr_arg
  intro x
  intro y
  apply comm

/- ACTUAL PROOF OF List.zipWith_comm_of_comm -/

example (f : α → α → β) (comm : ∀ x y : α, f x y = f y x) (l l' : List α) :
    zipWith f l l' = zipWith f l' l := by
  rw [zipWith_comm]
  simp only [comm]
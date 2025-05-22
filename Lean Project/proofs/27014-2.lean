import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example : (zipWith f l l').tail = zipWith f l.tail l'.tail := by
  cases l with
  | nil =>
    cases l' with
    | nil => rfl
    | _:: _ => rfl
  | _ :: ls =>
    cases l' with
    | nil => rfl
    | _ :: ls' =>
      simp [zipWith, tail]
      exact zipWith_tail f ls ls'

/- ACTUAL PROOF OF List.tail_zipWith -/

example : (zipWith f l l').tail = zipWith f l.tail l'.tail := by
  rw [← drop_one]; simp [drop_zipWith]
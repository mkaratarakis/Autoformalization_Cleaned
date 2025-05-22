import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example : (zipWith f l l').tail = zipWith f l.tail l'.tail := by
  cases l with
  | nil =>
    cases l' with
    | nil => rfl
    | _ :: _ => rfl
  | x :: xs =>
    cases l' with
    | nil => rfl
    | y :: ys =>
      simp [zipWith, tail]
      exact zipWith_tail f xs ys

/- ACTUAL PROOF OF List.tail_zipWith -/

example : (zipWith f l l').tail = zipWith f l.tail l'.tail := by
  rw [← drop_one]; simp [drop_zipWith]
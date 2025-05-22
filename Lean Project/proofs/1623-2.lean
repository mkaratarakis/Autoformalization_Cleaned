import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (xs ys : List α) : zipIdx (xs ++ ys) = zipIdx xs ++ zipIdxFrom xs.length ys := by
  rw [zipIdx_append]
  rfl

/- ACTUAL PROOF OF List.enum_append -/

example (xs ys : List α) : enum (xs ++ ys) = enum xs ++ enumFrom xs.length ys := by
  simp [enum, enumFrom_append]
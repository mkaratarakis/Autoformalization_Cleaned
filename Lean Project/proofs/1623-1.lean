import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (xs ys : List α) : enum (xs ++ ys) = enum xs ++ enumFrom xs.length ys := by
  rw [enum]
  rw [enumFrom_append]
  rw [zero_add]
  rw [←enum]
  rw [←enumFrom]

/- ACTUAL PROOF OF List.enum_append -/

example (xs ys : List α) : enum (xs ++ ys) = enum xs ++ enumFrom xs.length ys := by
  simp [enum, enumFrom_append]
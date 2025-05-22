import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (xs ys : List α) : zipIdx (xs ++ ys) = zipIdx xs ++ (zipIdx ys).map (Prod.map id (· + xs.length)) := by
  rw [zipIdx_append]
  rw [add_comm]
  rfl

/- ACTUAL PROOF OF List.enum_append -/

example (xs ys : List α) : enum (xs ++ ys) = enum xs ++ enumFrom xs.length ys := by
  simp [enum, enumFrom_append]
import Init.ByCases
import Init.Data.Nat.MinMax

open Nat



example ( a b : Nat) : a ≤ max a b := by
  by_cases (a <= b) <;> simp [Nat.max_def, *]
import Init.Data.List.Lemmas
import Init.Data.List.MinMax

open List
open Nat


example {xs : List α} [Min α] : xs.minimum? = none ↔ xs = [] := by
  cases xs <;> simp [minimum?]
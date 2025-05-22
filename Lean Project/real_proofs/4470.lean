import Init.Data.List.Lemmas
import Init.Data.List.MinMax

open List
open Nat


example {xs : List α} [Max α] : xs.maximum? = none ↔ xs = [] := by
  cases xs <;> simp [maximum?]
import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example (a b : Int) : a ≤ max a b := by
  rw [Int.max_def]; split <;> simp [*]
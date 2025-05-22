import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat


example {xs : List α} (w : xs.get? (xs.findIdx p) = some y) : p y := by
  induction xs with
  | nil => simp_all
  | cons x xs ih => by_cases h : p x <;> simp_all [findIdx_cons]
import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a : Int} (h : 0 ≤ a) : (toNat a : Int) = a := by
  rw [toNat_eq_max, Int.max_eq_left h]
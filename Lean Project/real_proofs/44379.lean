import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example (a : Int) : a ≤ toNat a := by
  rw [toNat_eq_max]; apply Int.le_max_left
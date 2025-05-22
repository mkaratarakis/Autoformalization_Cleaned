import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a : Int} (h : 0 ≤ a) : ∃ n : Nat, a = n := by
  have t := le.dest_sub h; rwa [Int.sub_zero] at t
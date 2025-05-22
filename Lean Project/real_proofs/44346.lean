import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a : Int} (h : 0 < a) : -a < 0 := by
  have : -a < -0 := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this
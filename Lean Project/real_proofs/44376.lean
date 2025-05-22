import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a b : Int} (h : -a ≤ b) : -b ≤ a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h
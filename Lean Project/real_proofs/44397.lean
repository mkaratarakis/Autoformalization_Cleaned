import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a b c : Int} (h : a + b ≤ c) : b ≤ c - a := by
  have h := Int.add_le_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h
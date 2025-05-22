import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a b c : Int} (h : b < c - a) : a + b < c := by
  have h := Int.add_lt_add_left h a
  rwa [← Int.add_sub_assoc, Int.add_comm a c, Int.add_sub_cancel] at h
import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example (m : Nat) : -[m+1] = -m - 1 := by
  simp only [negSucc_eq, Int.neg_add]; rfl
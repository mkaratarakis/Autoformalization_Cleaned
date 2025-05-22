import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {n m : Nat} : (↑n : Int) < ↑m ↔ n < m := by
  rw [lt_iff_add_one_le, ← ofNat_succ, ofNat_le]; rfl
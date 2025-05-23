import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (m : Nat) : -[m+1] = -m - 1 := by
  rw [Int.negSucc, Int.neg_add, Int.neg_one, Int.add_neg_one, Int.neg_neg, Int.coe_nat_add, Int.coe_nat_one]

/- ACTUAL PROOF OF Int.negSucc_eq' -/

example (m : Nat) : -[m+1] = -m - 1 := by
  simp only [negSucc_eq, Int.neg_add]; rfl
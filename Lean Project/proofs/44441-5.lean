import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (m : Nat) : -[m+1] = -m - 1 := by
  simp only [Int.negSucc]
  rw [Int.neg_add]
  rw [Int.add_neg_one]
  rw [Int.neg_neg]
  rw [Int.coe_nat_add]
  rw [Int.coe_nat_one]
  rfl

/- ACTUAL PROOF OF Int.negSucc_eq' -/

example (m : Nat) : -[m+1] = -m - 1 := by
  simp only [negSucc_eq, Int.neg_add]; rfl
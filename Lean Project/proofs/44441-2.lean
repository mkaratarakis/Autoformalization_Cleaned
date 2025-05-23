import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (m : Nat) : -[m+1] = -m - 1 := by
  rw [Int.negSucc]
  rw [Int.coe_nat_succ]
  rw [Int.neg_add]
  rw [Int.coe_nat_zero]
  apply Int.neg_neg

/- ACTUAL PROOF OF Int.negSucc_eq' -/

example (m : Nat) : -[m+1] = -m - 1 := by
  simp only [negSucc_eq, Int.neg_add]; rfl
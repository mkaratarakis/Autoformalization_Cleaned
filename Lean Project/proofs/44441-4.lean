import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (m : Nat) : -[m+1] = -m - 1 := by
  simp only [Int.negSucc, Int.coe_nat_succ, Int.neg_add]
  rw [Int.add_neg_one]

/- ACTUAL PROOF OF Int.negSucc_eq' -/

example (m : Nat) : -[m+1] = -m - 1 := by
  simp only [negSucc_eq, Int.neg_add]; rfl
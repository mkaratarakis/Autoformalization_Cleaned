import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example (n : Nat) : 0 ≤ -[n+1] ↔ False := by
  simp only [Int.not_le, iff_false]; exact Int.negSucc_lt_zero n
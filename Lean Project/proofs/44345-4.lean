import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (n : Nat) : 0 ≤ -[n+1] ↔ False := by
  constructor
  · intro h
    have : -[n+1] < 0 := by
      rw [negSucc_eq_negSucc]
      simp
    linarith
  · exact False.elim

/- ACTUAL PROOF OF Int.negSucc_not_nonneg -/

example (n : Nat) : 0 ≤ -[n+1] ↔ False := by
  simp only [Int.not_le, iff_false]; exact Int.negSucc_lt_zero n
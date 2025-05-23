import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (z : Int) : Int.sign (-z) = -Int.sign z := by
  by_cases hz : z = 0
  · simp only [hz, sign_zero, neg_zero]
  by_cases hp : z > 0
  · have : -z < 0 := neg_pos_of_neg_neg_eq hp
    simp only [sign_neg_of_neg, sign_pos_of_pos hp, this]
  · have : z < 0 := lt_of_not_ge hp
    have : -z > 0 := neg_neg_of_pos_neg this
    simp only [sign_neg_of_pos, sign_neg_of_neg, this]

/- ACTUAL PROOF OF Int.sign_neg -/

example (z : Int) : Int.sign (-z) = -Int.sign z := by
  match z with | 0 | succ _ | -[_+1] => rfl
import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (z : Int) : Int.sign (-z) = -Int.sign z := by
  by_cases hz : z = 0
  · simp only [hz, sign_zero, neg_zero]
  by_cases hp : 0 < z
  · simp only [sign_neg_of_neg, sign_pos_of_pos hp, neg_lt_zero.mpr hp]
  · have : z < 0 := not_le.mp (mt (le_of_lt ?m_1) hp)
    simp only [sign_neg_of_pos, sign_neg_of_neg, neg_pos.mpr this]

/- ACTUAL PROOF OF Int.sign_neg -/

example (z : Int) : Int.sign (-z) = -Int.sign z := by
  match z with | 0 | succ _ | -[_+1] => rfl
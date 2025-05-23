import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : b ≤ a) : max a b = a := by
  unfold max
  rw [if_neg]
  apply not_le_of_lt
  exact h

/- ACTUAL PROOF OF Int.max_eq_left -/

example {a b : Int} (h : b ≤ a) : max a b = a := by
  rw [← Int.max_comm b a]; exact Int.max_eq_right h
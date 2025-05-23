import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : b ≤ a) : max a b = a := by
  apply max_of_le
  exact h

/- ACTUAL PROOF OF Int.max_eq_left -/

example {a b : Int} (h : b ≤ a) : max a b = a := by
  rw [← Int.max_comm b a]; exact Int.max_eq_right h
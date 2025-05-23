import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : -b + a ≤ c) : a ≤ b + c := by
  have h1 : b + (-b + a) = a := by
    rw [add_assoc, add_left_neg]
  have h2 := Int.add_le_add_left h b
  rwa [h1] at h2

/- ACTUAL PROOF OF Int.le_add_of_neg_add_le -/

example {a b c : Int} (h : -b + a ≤ c) : a ≤ b + c := by
  have h := Int.add_le_add_left h b
  rwa [Int.add_neg_cancel_left] at h
import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open le
open Nat

example {a b : Int} (n : Nat) (h : b - a = n) : a ≤ b := by
  rw [← h]
  apply le_of_sub_nonneg
  exact Nat.cast_nonneg n

/- ACTUAL PROOF OF Int.le.intro_sub -/

example {a b : Int} (n : Nat) (h : b - a = n) : a ≤ b := by
  simp [le_def, h]; constructor
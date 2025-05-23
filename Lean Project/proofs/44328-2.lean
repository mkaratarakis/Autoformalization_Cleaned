import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open le
open Nat

example {a b : Int} (n : Nat) (h : b - a = n) : a ≤ b := by
  rw [Int.sub_eq_add_neg] at h
  exact le_of_add_le_add_right (by rwa [Int.coe_nat_eq])

/- ACTUAL PROOF OF Int.le.intro_sub -/

example {a b : Int} (n : Nat) (h : b - a = n) : a ≤ b := by
  simp [le_def, h]; constructor
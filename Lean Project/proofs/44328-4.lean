import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open le
open Nat

example {a b : Int} (n : Nat) (h : b - a = n) : a ≤ b := by
  rw [Int.sub_eq_add_neg] at h
  rw [←h]
  exact Int.le_of_sub_nonneg (Int.coe_nat_nonneg n)

/- ACTUAL PROOF OF Int.le.intro_sub -/

example {a b : Int} (n : Nat) (h : b - a = n) : a ≤ b := by
  simp [le_def, h]; constructor
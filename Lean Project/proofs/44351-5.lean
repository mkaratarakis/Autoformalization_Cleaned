import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (h : 0 ≤ a) : ∃ n : Nat, a = n := by
  exists a.toNat
  rw [Int.ofNat_toNat h]

/- ACTUAL PROOF OF Int.eq_ofNat_of_zero_le -/

example {a : Int} (h : 0 ≤ a) : ∃ n : Nat, a = n := by
  have t := le.dest_sub h; rwa [Int.sub_zero] at t
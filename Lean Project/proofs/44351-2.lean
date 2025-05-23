import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (h : 0 ≤ a) : ∃ n : Nat, a = n := by
  use a.toNat
  exact Int.toNat_of_nonneg h

/- ACTUAL PROOF OF Int.eq_ofNat_of_zero_le -/

example {a : Int} (h : 0 ≤ a) : ∃ n : Nat, a = n := by
  have t := le.dest_sub h; rwa [Int.sub_zero] at t
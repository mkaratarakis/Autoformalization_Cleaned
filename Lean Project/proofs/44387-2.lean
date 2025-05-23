import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {n : Nat} {z : Int} (h : 0 ≤ z) : n ≤ z.toNat ↔ (n : Int) ≤ z := by
  constructor
  · intro hn
    exact Int.coe_nat_le.2 hn
  · intro hn
    exact Int.coe_nat_le.1 hn

/- ACTUAL PROOF OF Int.le_toNat -/

example {n : Nat} {z : Int} (h : 0 ≤ z) : n ≤ z.toNat ↔ (n : Int) ≤ z := by
  rw [← Int.ofNat_le, Int.toNat_of_nonneg h]
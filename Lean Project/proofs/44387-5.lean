import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {n : Nat} {z : Int} (h : 0 ≤ z) : n ≤ z.toNat ↔ (n : Int) ≤ z := by
  constructor
  · intro hn
    rw [Int.ofNat_toNat h]
    exact_mod_cast hn
  · intro hn
    exact Nat.le_of_int_le_of_nonneg h hn

/- ACTUAL PROOF OF Int.le_toNat -/

example {n : Nat} {z : Int} (h : 0 ≤ z) : n ≤ z.toNat ↔ (n : Int) ≤ z := by
  rw [← Int.ofNat_le, Int.toNat_of_nonneg h]
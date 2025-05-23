import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {n m : Nat} : (↑n : Int) < ↑m ↔ n < m := by
  constructor
  · intro h
    have h' : (n : Int) + 1 ≤ m := by
      rw [←ofNat_one, ←ofNat_add]
      exact Int.add_one_le_of_lt h
    rw [←ofNat_one, ←ofNat_add, ofNat_le] at h'
    exact Nat.lt_of_add_one_le h'
  · intro h
    rw [←ofNat_one, ←ofNat_add, ofNat_le]
    apply ofNat_le.mpr
    exact Nat.lt_iff_add_one_le.mp h

/- ACTUAL PROOF OF Int.ofNat_lt -/

example {n m : Nat} : (↑n : Int) < ↑m ↔ n < m := by
  rw [lt_iff_add_one_le, ← ofNat_succ, ofNat_le]; rfl
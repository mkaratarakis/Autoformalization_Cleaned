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
      apply Int.add_one_le_of_lt
      exact h
    rw [←ofNat_one, ←ofNat_add] at h'
    apply Nat.lt_of_add_one_le
    apply ofNat_le_of_ofNat_le
    exact h'
  · intro h
    have h' : n + 1 ≤ m := Nat.lt_iff_add_one_le.mp h
    rw [←ofNat_one, ←ofNat_add, ofNat_le]
    exact h'

/- ACTUAL PROOF OF Int.ofNat_lt -/

example {n m : Nat} : (↑n : Int) < ↑m ↔ n < m := by
  rw [lt_iff_add_one_le, ← ofNat_succ, ofNat_le]; rfl
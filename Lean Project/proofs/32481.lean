import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a : Nat) {m n : Nat} (h : m ≤ n) :
    a ^ (n - m) * a ^ m = a ^ n := by
  rw [← Nat.pow_add]
  simp only [Nat.sub_add_cancel h]

/- ACTUAL PROOF OF Nat.pow_sub_mul_pow -/

example (a : Nat) {m n : Nat} (h : m ≤ n) :
    a ^ (n - m) * a ^ m = a ^ n := by
  rw [← Nat.pow_add, Nat.sub_add_cancel h]
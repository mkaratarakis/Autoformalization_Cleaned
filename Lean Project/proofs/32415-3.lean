import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {m n : Nat} : min n (min m n) = min n m := by
  cases h:le_total n m with
  | inl hnm =>
    rw [min_eq_left hnm, min_eq_left hnm]
  | inr hmn =>
    rw [min_eq_right hmn, min_eq_right hmn]

/- ACTUAL PROOF OF Nat.min_self_assoc' -/

example {m n : Nat} : min n (min m n) = min n m := by
  rw [Nat.min_comm m n, ← Nat.min_assoc, Nat.min_self]
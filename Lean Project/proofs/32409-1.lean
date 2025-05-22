import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {m n : Nat} : min m (min m n) = min m n := by
  rw [min_assoc]
  rw [min_self]
  rfl

/- ACTUAL PROOF OF Nat.min_self_assoc -/

example {m n : Nat} : min m (min m n) = min m n := by
  rw [← Nat.min_assoc, Nat.min_self]
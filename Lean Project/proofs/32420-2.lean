import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b c : Nat} : a - b ≤ c ↔ a ≤ b + c := by
  rw [Nat.sub_le_iff_le_add]
  exact Iff.rfl

/- ACTUAL PROOF OF Nat.sub_le_iff_le_add' -/

example {a b c : Nat} : a - b ≤ c ↔ a ≤ b + c := by
  rw [Nat.add_comm, Nat.sub_le_iff_le_add]
import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (c : Bool) : c.toNat ≤ 1 := by
  cases c
  · exact Nat.zero_le 1
  · exact Nat.le_refl 1

/- ACTUAL PROOF OF Bool.toNat_le -/

example (c : Bool) : c.toNat ≤ 1 := by
  cases c <;> trivial
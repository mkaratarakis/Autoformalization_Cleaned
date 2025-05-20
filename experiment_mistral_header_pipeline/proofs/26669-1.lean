import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Multiset

open Multiset
variable {α : Type*}
variable [Preorder α] [LocallyFiniteOrder α] {a b x : α}

example : x ∈ Ioo a b ↔ a < x ∧ x < b := by
  rw [mem_Ioo]
  rfl

/- ACTUAL PROOF OF Multiset.mem_Ioo -/

example : x ∈ Ioo a b ↔ a < x ∧ x < b := by
  rw [Ioo, ← Finset.mem_def, Finset.mem_Ioo]
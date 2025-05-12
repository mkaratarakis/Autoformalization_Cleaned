import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Multiset

open Multiset
variable {α : Type*}
variable [Preorder α] [LocallyFiniteOrder α] {a b x : α}

example : x ∈ Ioo a b ↔ a < x ∧ x < b := by
  -- First, we use the definition of the open-open interval multiset
  rw [Ioo]
  -- Next, we use the fact that membership in a finite set is equivalent to membership in its underlying multiset
  rw [mem_filter]
  -- Finally, we use the theorem that states membership in the open-open interval finite set is equivalent to the given condition
  rw [Finset.mem_Ioo]
  rfl

/- ACTUAL PROOF OF Multiset.mem_Ioo -/

example : x ∈ Ioo a b ↔ a < x ∧ x < b := by
  rw [Ioo, ← Finset.mem_def, Finset.mem_Ioo]
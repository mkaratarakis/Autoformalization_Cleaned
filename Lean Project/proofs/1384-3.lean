import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example {a b : Nat} : compare a b = .gt ↔ b < a := by
  constructor
  · intro h
    unfold compare at h
    cases h
    case eq =>
      · exact absurd rfl h.eq
      · exact Nat.lt_of_sub_eq_zero h.isSome
  · intro h
    unfold compare
    rw [Nat.sub_eq_zero_iff_le]
    exact Or.inl (Nat.zero_eq_of_lt h)

/- ACTUAL PROOF OF Nat.compare_eq_gt -/

example {a b : Nat} : compare a b = .gt ↔ b < a := by
  rw [compare_def_lt]; (repeat' split) <;> simp [Nat.le_of_lt, *]
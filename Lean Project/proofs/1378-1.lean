import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example (a b : Nat) : (compare a b).swap = compare b a := by
  unfold compare
  split
  · intro h1 h2
    rw [swap_eq]
    simp [compare]
    rfl
  · intro h1
    split
    · intro h2
      rw [swap_lt]
      simp [compare]
      rfl
    · intro h2
      rw [swap_gt]
      simp [compare]
      rfl

/- ACTUAL PROOF OF Nat.compare_swap -/

example (a b : Nat) : (compare a b).swap = compare b a := by
  simp only [compare_def_le]; (repeat' split) <;> try rfl
  next h1 h2 => cases h1 (Nat.le_of_not_le h2)
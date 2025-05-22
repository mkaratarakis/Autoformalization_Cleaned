import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example (a b : Nat) : (compare a b).swap = compare b a := by
  unfold compare
  cases h : decide (a ≤ b) <;> cases h' : decide (b ≤ a)
  · -- Case: a ≤ b and b ≤ a
    simp [h, h', Ordering.swap]
  · -- Case: a ≤ b and ¬ b ≤ a
    simp [h, h', Ordering.swap]
  · -- Case: ¬ a ≤ b and b ≤ a
    simp [h, h', Ordering.swap]
  · -- Case: ¬ a ≤ b and ¬ b ≤ a
    simp [h, h', Ordering.swap]

/- ACTUAL PROOF OF Nat.compare_swap -/

example (a b : Nat) : (compare a b).swap = compare b a := by
  simp only [compare_def_le]; (repeat' split) <;> try rfl
  next h1 h2 => cases h1 (Nat.le_of_not_le h2)
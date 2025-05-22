import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {a : α} :
    isSuffixOf l (replicate n a) = (decide (l.length ≤ n) && l.all (· == a)) := by
  unfold isSuffixOf
  unfold decide
  unfold List.all
  unfold BEq.beq
  simp [replicate, List.length]
  split
  · intro h
    simp [h]
    split
    · exact Nat.le_of_lt_succ h
    · induction l generalizing n
      · simp
      · simp [*]
        split
        · exact Nat.le_of_lt_succ h_a_1
        · intro x hx
          simp [*]
  · intro h
    simp [h]
    split
    · exact Nat.lt_of_le_succ h
    · induction l generalizing n
      · simp
      · simp [*]
        split
        · exact Nat.le_of_lt_succ h_a_1
        · intro x hx
          simp [*]

/- ACTUAL PROOF OF List.isSuffixOf_replicate -/

example {a : α} :
    isSuffixOf l (replicate n a) = (decide (l.length ≤ n) && l.all (· == a)) := by
  simp [isSuffixOf, all_eq]
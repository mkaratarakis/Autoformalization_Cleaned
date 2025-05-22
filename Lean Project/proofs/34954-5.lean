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
    induction l generalizing n
    · simp
    · simp [*]
      exact And.intro (Nat.le_of_lt_succ h_a_1) (And.intro rfl h_ih)
  · intro h
    induction l generalizing n
    · simp
    · simp [*]
      exact And.intro (Nat.le_of_lt_succ h_a_1) (And.intro rfl h_ih)

/- ACTUAL PROOF OF List.isSuffixOf_replicate -/

example {a : α} :
    isSuffixOf l (replicate n a) = (decide (l.length ≤ n) && l.all (· == a)) := by
  simp [isSuffixOf, all_eq]
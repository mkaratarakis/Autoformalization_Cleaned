import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]

example {a : α} :
    isPrefixOf l (replicate n a) = (decide (l.length ≤ n) && l.all (· == a)) := by
  induction l with
  | nil =>
    simp [isPrefixOf, replicate, decide, and_true]
  | cons h t ih =>
    cases n with
    | zero =>
      simp [isPrefixOf, replicate, decide, and_false]
    | succ m =>
      simp [isPrefixOf, replicate]
      split
      · intro h1
        simp [h1, ih]
        split
        · apply Nat.le_succ_of_le
        · intro x h2
          exact h2
      · intro h1
        simp [h1]
        split
        · exact Nat.zero_le _
        · intro x h2
          cases x
          · contradiction
          · exact h2

/- ACTUAL PROOF OF List.isPrefixOf_replicate -/

example {a : α} :
    isPrefixOf l (replicate n a) = (decide (l.length ≤ n) && l.all (· == a)) := by
  induction l generalizing n with
  | nil => simp
  | cons h t ih =>
    cases n
    · simp
    · simp [replicate_succ, isPrefixOf_cons₂, ih, Nat.succ_le_succ_iff, Bool.and_left_comm]
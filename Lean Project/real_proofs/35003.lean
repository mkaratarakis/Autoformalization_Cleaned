import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]


example {a : α} :
    isPrefixOf l (replicate n a) = (decide (l.length ≤ n) && l.all (· == a)) := by
  induction l generalizing n with
  | nil => simp
  | cons h t ih =>
    cases n
    · simp
    · simp [replicate_succ, isPrefixOf_cons₂, ih, Nat.succ_le_succ_iff, Bool.and_left_comm]
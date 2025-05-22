import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example : find? p l = none ↔ ∀ x ∈ l, ¬ p x := by
  induction l with
  | nil =>
    simp [find?, not_false_eq_true, forall_mem_nil]
  | cons a l ih =>
    by_cases hp : p a
    · simp [hp, find?, if_true, not_false_eq_true, forall_mem_cons]
    · simp [hp, find?, if_false, ih, not_true_eq_false, forall_mem_cons]

/- ACTUAL PROOF OF List.find?_eq_none -/

example : find? p l = none ↔ ∀ x ∈ l, ¬ p x := by
  induction l <;> simp [find?_cons]; split <;> simp [*]
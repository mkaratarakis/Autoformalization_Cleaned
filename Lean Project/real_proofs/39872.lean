import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat


example : find? p l = none ↔ ∀ x ∈ l, ¬ p x := by
  induction l <;> simp [find?_cons]; split <;> simp [*]
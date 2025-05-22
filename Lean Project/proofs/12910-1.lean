import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]

example (a b : α) : count a [b] = if b == a then 1 else 0 := by
    unfold count
    simp [count]
    cases h : b == a <;> simp [h]
    exact if_pos rfl
    exact if_neg (ne_of_eq_of_ne h)

/- ACTUAL PROOF OF List.count_singleton -/

example (a b : α) : count a [b] = if b == a then 1 else 0 := by
  simp [count_cons]
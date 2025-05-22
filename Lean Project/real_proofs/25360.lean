import Init.BinderPredicates
import Init.Data.Bool

open Bool



example [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    (a == b) = decide (a = b) := by
  cases h : a == b
  · simp [ne_of_beq_false h]
  · simp [eq_of_beq h]
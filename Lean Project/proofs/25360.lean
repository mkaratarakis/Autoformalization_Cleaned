import Init.BinderPredicates
import Init.Data.Bool

open Bool


example [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    (a == b) = decide (a = b) := by
  cases h : (a == b)
  · have : a ≠ b := ne_of_beq_false h
    simp [h, this]
  · have : a = b := eq_of_beq h
    simp [h, this]

/- ACTUAL PROOF OF Bool.beq_eq_decide_eq -/

example [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    (a == b) = decide (a = b) := by
  cases h : a == b
  · simp [ne_of_beq_false h]
  · simp [eq_of_beq h]
import Init.Tactics
import Init.SizeOf

open Bool


example (b : Bool) : sizeOf b = 1 := by
  cases b <;> rfl

/- ACTUAL PROOF OF Bool.sizeOf_eq_one -/

example (b : Bool) : sizeOf b = 1 := by
  cases b <;> rfl
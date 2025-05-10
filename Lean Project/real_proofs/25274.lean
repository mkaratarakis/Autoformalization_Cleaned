import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : {b : Bool} → b = false ↔ b ≠ true := by
  decide
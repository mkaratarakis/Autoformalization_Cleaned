import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(b : Bool), ((!b) = b) ↔ False := by
  decide
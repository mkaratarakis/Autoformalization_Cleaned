import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(b:Bool), (b = true → b = false) ↔ (b = false) := by
  decide
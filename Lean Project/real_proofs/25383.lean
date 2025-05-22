import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(b:Bool), (b = false → b = true) ↔ (b = true) := by
  decide
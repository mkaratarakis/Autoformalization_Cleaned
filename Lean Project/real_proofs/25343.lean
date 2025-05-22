import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x : Bool), x ≤ true := by
  decide
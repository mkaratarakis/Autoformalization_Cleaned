import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ {x : Bool}, true ≤ x → x = true := by
  decide
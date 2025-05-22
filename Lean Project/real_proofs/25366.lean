import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ {x : Bool}, x ≤ false → x = false := by
  decide
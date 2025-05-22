import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ {x y z : Bool}, x < y → y < z → x < z := by
  decide
import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ {m x y : Bool}, (x && m) = (y && m) → (x || m) = (y || m) → x = y := by
  decide
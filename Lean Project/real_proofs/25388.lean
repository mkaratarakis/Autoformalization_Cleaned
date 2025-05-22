import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ {m x y : Bool}, (m && x) = (m && y) → (m || x) = (m || y) → x = y := by
  decide
import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y z : Bool}, x ≤ y → y ≤ z → x ≤ z := by
  decide

/- ACTUAL PROOF OF Bool.le_trans -/

example : ∀ {x y z : Bool}, x ≤ y → y ≤ z → x ≤ z := by
  decide
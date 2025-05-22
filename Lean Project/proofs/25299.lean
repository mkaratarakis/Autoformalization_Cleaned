import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), (xor x y && z) = xor (x && z) (y && z) := by
  decide

/- ACTUAL PROOF OF Bool.and_xor_distrib_right -/

example : ∀ (x y z : Bool), (xor x y && z) = xor (x && z) (y && z) := by
  decide
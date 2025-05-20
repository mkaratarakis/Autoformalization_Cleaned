import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : {b : Bool} → b ≠ false ↔ b = true := by
  apply Iff.intro
  · intro h
    cases b
    · ex falso h
    · exact rfl
  · intro h
    cases h
    · norm_num

/- ACTUAL PROOF OF Bool.ne_false_iff -/

example : {b : Bool} → b ≠ false ↔ b = true := by
  decide
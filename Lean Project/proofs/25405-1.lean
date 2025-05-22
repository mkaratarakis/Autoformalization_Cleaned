import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (b : Bool) : b.toNat = 0 ↔ b = false := by
  cases b
  · {
    constructor
    · exact rfl
    · exact rfl
    }
  · {
    constructor
    · contradiction
    · exact False.elim
    }

/- ACTUAL PROOF OF Bool.toNat_eq_zero -/

example (b : Bool) : b.toNat = 0 ↔ b = false := by
  cases b <;> simp
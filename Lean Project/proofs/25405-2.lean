import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (b : Bool) : b.toNat = 0 ↔ b = false := by
  cases b
  · {
    constructor
    · intro h
      exact h
    · intro h
      rw [h]
      exact rfl
    }
  · {
    constructor
    · intro h
      contradiction
    · intro h
      exfalso
      exact h
    }

/- ACTUAL PROOF OF Bool.toNat_eq_zero -/

example (b : Bool) : b.toNat = 0 ↔ b = false := by
  cases b <;> simp
import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (c : Bool) : c.toNat ≤ 1 := by
  cases c <;> trivial
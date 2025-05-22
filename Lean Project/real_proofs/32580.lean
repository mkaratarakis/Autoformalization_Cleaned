import Init.Core
import Init.SimpLemmas

open Bool



example (b : Bool) : (b || false) = b := by
  cases b <;> rfl
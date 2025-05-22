import Init.Core
import Init.SimpLemmas

open Bool



example (b : Bool) : (b && false) = false := by
  cases b <;> rfl
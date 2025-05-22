import Init.Core
import Init.SimpLemmas

open Bool



example (b : Bool) : (false && b) = false := by
  cases b <;> rfl
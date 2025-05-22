import Init.Core
import Init.SimpLemmas

open Bool



example (b : Bool) : (false || b) = b := by
  cases b <;> rfl
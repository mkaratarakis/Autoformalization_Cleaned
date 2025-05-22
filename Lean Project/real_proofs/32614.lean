import Init.Core
import Init.SimpLemmas

open Bool



example (b : Bool) : (¬(b = false)) = (b = true) := by
  cases b <;> decide
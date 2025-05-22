import Init.Core
import Init.SimpLemmas

open Bool



example (b : Bool) : (true || b) = true := by
  cases b <;> rfl
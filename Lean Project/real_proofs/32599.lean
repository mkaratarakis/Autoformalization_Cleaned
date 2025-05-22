import Init.Core
import Init.SimpLemmas

open Bool



example (b : Bool) : (b && true) = b := by
  cases b <;> rfl
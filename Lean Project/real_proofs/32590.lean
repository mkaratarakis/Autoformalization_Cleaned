import Init.Core
import Init.SimpLemmas

open Bool



example (b : Bool) : (b || true) = true := by
  cases b <;> rfl
import Init.Core
import Init.SimpLemmas

open Bool



example (b : Bool) : (!!b) = b := by
  cases b <;> rfl
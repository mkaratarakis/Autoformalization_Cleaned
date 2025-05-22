import Init.Core
import Init.SimpLemmas

open Bool



example (a b : Bool) : (a == b) = (a = b) := by
  simp
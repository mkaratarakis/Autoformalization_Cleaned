import Init.Core
import Init.SimpLemmas

open Bool



example (a b c : Bool) : (a || b || c) = (a || (b || c)) := by
  cases a <;> cases b <;> cases c <;> decide
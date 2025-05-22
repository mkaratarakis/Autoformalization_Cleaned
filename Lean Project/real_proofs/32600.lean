import Init.Core
import Init.SimpLemmas





example (b : Bool) : (b == true)  =  b := by
  cases b <;> rfl
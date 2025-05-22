import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example (x : Option α) : x.bind some = x := by
  cases x
  . case none =>
    simp [bind]
  . case some a =>
    simp [bind]

/- ACTUAL PROOF OF Option.bind_some -/

example (x : Option α) : x.bind some = x := by
  cases x <;> rfl
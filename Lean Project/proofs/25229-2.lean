import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example {x : Option α} : (x.map f).isSome = x.isSome := by

  cases x
  case none =>
    simp
    rfl
  case some a =>
    simp
    rfl

/- ACTUAL PROOF OF Option.isSome_map' -/

example {x : Option α} : (x.map f).isSome = x.isSome := by
  cases x <;> simp
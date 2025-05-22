import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example {x : Option α} : (x.map f).isSome = x.isSome := by
  cases x <;> simp
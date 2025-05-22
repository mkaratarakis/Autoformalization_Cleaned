import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example {x : Option (Option (Option α))} : x.join.join = (x.map join).join := by
  cases x <;> simp
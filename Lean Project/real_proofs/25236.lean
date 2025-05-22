import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example {f : α → β} {x : Option (Option α)} :
    (x.map (Option.map f)).join = x.join.map f := by
  cases x <;> simp
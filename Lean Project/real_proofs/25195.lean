import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example {x : Option α} (hx : x ≠ none) (y : α) : some (x.getD y) = x := by
  cases x; {contradiction}; rw [getD_some]
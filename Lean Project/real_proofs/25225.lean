import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example (x : Option α) : (x <|> none) = x := by
  cases x <;> rfl
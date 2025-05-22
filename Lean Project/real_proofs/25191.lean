import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example : isSome a = false ↔ a.isNone = true := by
  cases a <;> simp
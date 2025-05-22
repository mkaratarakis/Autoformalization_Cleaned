import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example {o : Option α} {a b} : o.getD a = b ↔ (o = some b ∨ o = none ∧ a = b) := by
  cases o <;> simp
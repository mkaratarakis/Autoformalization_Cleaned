import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example : x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp
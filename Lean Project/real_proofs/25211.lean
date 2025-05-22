import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example : isSome x ↔ ∃ a, x = some a := by
  cases x <;> simp [isSome]
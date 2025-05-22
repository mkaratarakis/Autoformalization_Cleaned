import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ a, o = some a → f a = none := by
  cases o <;> simp
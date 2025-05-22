import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example {f} {b : Option α} : liftOrGet f none b = b := by
  cases b <;> rfl
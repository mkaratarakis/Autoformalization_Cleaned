import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example (x : Option α) : x.bind (fun _ => none (α := β)) = none := by
  cases x <;> rfl
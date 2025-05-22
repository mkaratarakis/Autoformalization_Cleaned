import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example {f} {a : Option α} : liftOrGet f a none = a := by
  cases a <;> rfl

/- ACTUAL PROOF OF Option.liftOrGet_none_right -/

example {f} {a : Option α} : liftOrGet f a none = a := by
  cases a <;> rfl
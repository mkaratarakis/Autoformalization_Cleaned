import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example : or o none = o := by
  cases o
  case none =>
    rfl
  case some x =>
    rfl

/- ACTUAL PROOF OF Option.or_none -/

example : or o none = o := by
  cases o <;> rfl
import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example {x y : Option α} : (x <|> y).map f = (x.map f <|> y.map f) := by
  cases x <;> simp [Option.map, Option.orElse]

/- ACTUAL PROOF OF Option.map_orElse -/

example {x y : Option α} : (x <|> y).map f = (x.map f <|> y.map f) := by
  cases x <;> simp
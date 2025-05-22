import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example {x : Option (Option (Option α))} : x.join.join = (x.map join).join := by
  cases x
  case none =>
    repeat rw [join]
  case some y =>
    cases y
    case none =>
      repeat rw [join]
    case some z =>
      rw [join, map]
      rw [join]

/- ACTUAL PROOF OF Option.join_join -/

example {x : Option (Option (Option α))} : x.join.join = (x.map join).join := by
  cases x <;> simp
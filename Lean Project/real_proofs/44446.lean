import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example (z : Int) : Int.sign (-z) = -Int.sign z := by
  match z with | 0 | succ _ | -[_+1] => rfl
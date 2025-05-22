import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Fin.Basic
import Init.Data.UInt.Basic
import Init.Data.Repr
import Init.Data.ToString.Basic
import Init.GetElem
import Init.Data.Array.Basic

open Array
open reverse
variable {α : Type u}


example {i j : Nat} (h : i < j) : j - 1 - (i + 1) < j - i := by
  rw [Nat.sub_sub, Nat.add_comm]
  exact Nat.lt_of_le_of_lt (Nat.pred_le _) (Nat.sub_succ_lt_self _ _ h)
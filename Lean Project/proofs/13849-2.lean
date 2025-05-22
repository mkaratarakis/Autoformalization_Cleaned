import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Fin.Basic
import Init.Data.UInt.Basic
import Init.Data.Repr
import Init.Data.ToString.Basic
import Init.GetElem
import Init.Data.Array.Basic

open Array
variable {α : Type u}

example (as : List α) : as.toArray.toList = as := by
  induction as with
  | nil =>
    simp [toArray]
  | cons a as ih =>
    simp [toArray, ih]

/- ACTUAL PROOF OF Array.data_toArray -/

example (as : List α) : as.toArray.data = as := by
  simp [List.toArray, Array.mkEmpty]
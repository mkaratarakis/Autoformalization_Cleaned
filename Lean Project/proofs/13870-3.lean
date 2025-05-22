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

example (as : List α) (acc : Array α) : (as.toArrayAux acc).toList = acc.toList ++ as := by
  induction as with
  | nil =>
    rfl
  | cons head tail ih =>
    rw [List.toArrayAux, ih]
    simp [Array.push, List.cons_append]

/- ACTUAL PROOF OF Array.toArrayAux_eq -/

example (as : List α) (acc : Array α) : (as.toArrayAux acc).data = acc.data ++ as := by
  induction as generalizing acc <;> simp [*, List.toArrayAux, Array.push, List.append_assoc, List.concat_eq_append]
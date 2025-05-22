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

example {as bs : Array α} (h : as.data = bs.data) : as = bs := by
  unfold Array.data at h
  simp [Array.data]
  rw [h]
  simp

/- ACTUAL PROOF OF Array.ext' -/

example {as bs : Array α} (h : as.data = bs.data) : as = bs := by
  cases as; cases bs; simp at h; rw [h]
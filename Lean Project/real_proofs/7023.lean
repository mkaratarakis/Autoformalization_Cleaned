import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List



example : @eraseP = @erasePTR := by
  funext α p l; simp [erasePTR]
  let rec go (acc) : ∀ xs, l = acc.data ++ xs →
    erasePTR.go p l xs acc = acc.data ++ xs.eraseP p
  | [] => fun h => by simp [erasePTR.go, eraseP, h]
  | x::xs => by
    simp [erasePTR.go, eraseP]; cases p x <;> simp
    · intro h; rw [go _ xs]; {simp}; simp [h]
  exact (go #[] _ rfl).symm
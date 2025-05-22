import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @eraseP = @erasePTR := by
  funext α p l
  induction l with
  | nil =>
    simp [eraseP, erasePTR, erasePTR.go, Array.toList]
  | cons x xs ih =>
    simp [eraseP, erasePTR, erasePTR.go, Array.toList]
    by_cases h : p x
    · simp [h, ih]
    · simp [h, ih]
      rw [Array.toList_cons]
      exact ih

/- ACTUAL PROOF OF List.eraseP_eq_erasePTR -/

example : @eraseP = @erasePTR := by
  funext α p l; simp [erasePTR]
  let rec go (acc) : ∀ xs, l = acc.data ++ xs →
    erasePTR.go p l xs acc = acc.data ++ xs.eraseP p
  | [] => fun h => by simp [erasePTR.go, eraseP, h]
  | x::xs => by
    simp [erasePTR.go, eraseP]; cases p x <;> simp
    · intro h; rw [go _ xs]; {simp}; simp [h]
  exact (go #[] _ rfl).symm
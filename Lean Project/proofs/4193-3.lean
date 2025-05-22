import Init.Data.BitVec.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Fin.Iterate
import Init.Data.BitVec.Folds

open BitVec
open iunfoldr


example 
    {f : Fin w → α → α × Bool} (state : Nat → α) (s : α)
    (init : s = state 0)
    (ind : ∀(i : Fin w), (f i (state i.val)).fst = state (i.val+1)) :
    (iunfoldr f s).fst = state w := by
  unfold iunfoldr
  let F := fun (i : Fin (w + 1)) (p : Fin (w - i.val) → α × BitVec i.width) =>
    (p ⟨0, i.isLt⟩).fst = state i.val
  have h : ∀ (i : Fin (w + 1)), F i := by
    apply Fin.hetiterElim
    · intro i hih
      rw [Fin.hetiterStep]
      rw [ind i]
      exact hih
    · exact init
  exact h ⟨w, Nat.le_refl _⟩ rfl

/- ACTUAL PROOF OF BitVec.iunfoldr.fst_eq -/

example 
    {f : Fin w → α → α × Bool} (state : Nat → α) (s : α)
    (init : s = state 0)
    (ind : ∀(i : Fin w), (f i (state i.val)).fst = state (i.val+1)) :
    (iunfoldr f s).fst = state w := by
  unfold iunfoldr
  apply Fin.hIterate_elim (fun i (p : α × BitVec i) => p.fst = state i)
  case init =>
    exact init
  case step =>
    intro i ⟨s, v⟩ p
    simp_all [ind i]
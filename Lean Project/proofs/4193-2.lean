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
  have h1 : iunfoldrAux f (s, nil) w = iunfoldr f s := by rfl
  rw [h1]
  have h2 : iunfoldrAux f (s, nil) w.fst = state w := by
    apply Fin.hetiterElim
    · intro i p
      exact (ind i p).1
    · exact init

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
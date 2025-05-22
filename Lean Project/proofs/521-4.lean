import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat

example {l : List α} (h : ∀ a, a ∈ l → ¬p a) : l.eraseP p = l := by
  induction l with
  | nil => rfl
  | cons a l' ih =>
    simp only [eraseP, ih]
    split
    · exact h a (mem_cons_self _ _)
    · rw [ih (fun b m => h b (mem_cons_of_mem _ m))]

/- ACTUAL PROOF OF List.eraseP_of_forall_not -/

example {l : List α} (h : ∀ a, a ∈ l → ¬p a) : l.eraseP p = l := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [h _ (.head ..), ih (forall_mem_cons.1 h).2]
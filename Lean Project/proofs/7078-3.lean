import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example (a : α) (m n : Nat) :
  replicateTR.loop a n (replicate m a) = replicate (n + m) a := by
  induction n with
  | zero =>
    simp [replicateTR.loop]
  | succ k ih =>
    simp [replicateTR.loop]
    rw [ih (m + 1)]
    exact replicate_succ_of_succ _ _ _

/- ACTUAL PROOF OF List.replicateTR_loop_replicate_eq -/

example (a : α) (m n : Nat) :
  replicateTR.loop a n (replicate m a) = replicate (n + m) a := by
  induction n generalizing m with simp [replicateTR.loop]
  | succ n ih => simp [Nat.succ_add]; exact ih (m+1)
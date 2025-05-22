import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example (a : α) (m n : Nat) :
  replicateTR.loop a n (replicate m a) = replicate (n + m) a := by
  induction n with
  | zero =>
    rfl
  | succ k ih =>
    specialize ih m
    rw [Nat.add_succ, replicateTR.loop, ih, Nat.add_assoc, Nat.add_comm (Nat.succ _), ← Nat.add_assoc]

/- ACTUAL PROOF OF List.replicateTR_loop_replicate_eq -/

example (a : α) (m n : Nat) :
  replicateTR.loop a n (replicate m a) = replicate (n + m) a := by
  induction n generalizing m with simp [replicateTR.loop]
  | succ n ih => simp [Nat.succ_add]; exact ih (m+1)
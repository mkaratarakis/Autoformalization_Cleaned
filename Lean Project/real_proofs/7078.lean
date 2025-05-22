import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List



example (a : α) (m n : Nat) :
  replicateTR.loop a n (replicate m a) = replicate (n + m) a := by
  induction n generalizing m with simp [replicateTR.loop]
  | succ n ih => simp [Nat.succ_add]; exact ih (m+1)
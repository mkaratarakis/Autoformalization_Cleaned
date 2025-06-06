import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {n : Nat} {a : α} :
    (replicate n a).Nodup ↔ n ≤ 1 := by
  constructor
  · intro h
    cases n
    · exact zero_le _
    · simp [replicate, Nodup] at h
      exact Nat.succ_le_succ (Nat.zero_le _)
  · intro h
    cases n
    · simp [replicate, Nodup]
    · simp [replicate, Nodup]
      exact Nat.le_antisymm h (Nat.le_succ_of_le_succ (Nat.zero_le _))

/- ACTUAL PROOF OF List.nodup_replicate -/

example {n : Nat} {a : α} :
    (replicate n a).Nodup ↔ n ≤ 1 := by
  simp [Nodup]
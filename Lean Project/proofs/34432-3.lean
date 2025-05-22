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
      exfalso
      apply h
      exact ⟨1, 1, rfl⟩
  · intro h
    cases n
    · simp [replicate, Nodup]
    · simp [replicate]
      exact Nodup.single _

/- ACTUAL PROOF OF List.nodup_replicate -/

example {n : Nat} {a : α} :
    (replicate n a).Nodup ↔ n ≤ 1 := by
  simp [Nodup]
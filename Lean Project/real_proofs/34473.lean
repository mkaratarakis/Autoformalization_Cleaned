import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example {l : List α} {k : Nat} : l.drop k = [] ↔ l.length ≤ k := by
  refine' ⟨fun h => _, drop_eq_nil_of_le⟩
  induction k generalizing l with
  | zero =>
    simp only [drop] at h
    simp [h]
  | succ k hk =>
    cases l
    · simp
    · simp only [drop] at h
      simpa [Nat.succ_le_succ_iff] using hk h
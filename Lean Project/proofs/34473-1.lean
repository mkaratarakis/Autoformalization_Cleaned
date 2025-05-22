import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l : List α} {k : Nat} : l.drop k = [] ↔ l.length ≤ k := by
  constructor
  · intro h
    induction k with
    | zero =>
      simp [drop] at h
      simp [h]
    | succ k ih =>
      cases l with
      | nil =>
        simp
      | cons _ _ =>
        simp [drop] at h
        simp [drop, List.length]
        apply Nat.succ_le_succ
        apply ih
        exact h
  · intro h
    apply drop_eq_nil_of_le h

/- ACTUAL PROOF OF List.drop_eq_nil_iff_le -/

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
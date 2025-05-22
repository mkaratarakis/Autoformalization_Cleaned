import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example : l <+ replicate m a ↔ ∃ n, n ≤ m ∧ l = replicate n a := by
  induction l with
  | nil =>
    simp [replicate]
    use 0
    simp [Nat.zero_le]
  | cons b l' ih =>
    constructor
    · intro h
      cases h with
      | inl h =>
        rcases ih h with ⟨n, hn, rfl⟩
        use n + 1
        simp [Nat.succ_le_succ_iff]
        simp [replicate, Nat.succ_eq_add_one]
      | inr h =>
        rcases ih h with ⟨n, hn, rfl⟩
        use n + 1
        simp [Nat.succ_le_succ_iff]
        simp [replicate, Nat.succ_eq_add_one]
    · rintro ⟨n, hn, rfl⟩
      cases n with
      | zero =>
        rcases ih ⟨0, Nat.zero_le _, rfl⟩ with ⟨k, hk, rfl⟩
        use k + 1
        simp [Nat.succ_le_succ_iff]
        simp [replicate, Nat.succ_eq_add_one]
      | succ n' =>
        rcases ih ⟨n', Nat.le_of_succ_le_succ hn, rfl⟩ with ⟨k, hk, rfl⟩
        use k + 1
        simp [Nat.succ_le_succ_iff]
        simp [replicate, Nat.succ_eq_add_one]

/- ACTUAL PROOF OF List.sublist_replicate_iff -/

example : l <+ replicate m a ↔ ∃ n, n ≤ m ∧ l = replicate n a := by
  induction l generalizing m with
  | nil =>
    simp only [nil_sublist, true_iff]
    exact ⟨0, zero_le m, by simp⟩
  | cons b l ih =>
    constructor
    · intro w
      cases m with
      | zero => simp at w
      | succ m =>
        simp [replicate_succ] at w
        cases w with
        | cons _ w =>
          obtain ⟨n, le, rfl⟩ := ih.1 (sublist_of_cons_sublist w)
          obtain rfl := (mem_replicate.1 (mem_of_cons_sublist w)).2
          exact ⟨n+1, Nat.add_le_add_right le 1, rfl⟩
        | cons₂ _ w =>
          obtain ⟨n, le, rfl⟩ := ih.1 w
          refine ⟨n+1, Nat.add_le_add_right le 1, by simp [replicate_succ]⟩
    · rintro ⟨n, le, w⟩
      rw [w]
      exact (replicate_sublist_replicate a).2 le
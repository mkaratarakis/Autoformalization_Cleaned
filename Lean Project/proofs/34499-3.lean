import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {n : Nat} {a : α} :
    (replicate n a).Pairwise R ↔ n ≤ 1 ∨ R a a := by
  induction n with
  | zero =>
    simp
    constructor
    · exact Nat.zero_le _
    · exact Or.inl (Nat.zero_le 1)
  | succ k ih =>
    simp [replicate]
    constructor
    · intro h
      by_cases hk : k = 0
      · rw [hk] at h
        exact Or.inl (by decide)
      · have : replicate k a = [] := by simp [hk]
        rw [this] at h
        exact Or.inr h
    · intro h
      by_cases hk : k = 0
      · rw [hk]
        exact ⟨fun h => (Nat.zero_ne_succ _ h).elim, Or.inl (by decide)⟩
      · have : replicate k a = [] := by simp [hk]
        rw [this]
        exact ⟨fun h => h, Or.inr h⟩

/- ACTUAL PROOF OF List.pairwise_replicate -/

example {n : Nat} {a : α} :
    (replicate n a).Pairwise R ↔ n ≤ 1 ∨ R a a := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate_succ, pairwise_cons, mem_replicate, ne_eq, and_imp,
      forall_eq_apply_imp_iff, ih]
    constructor
    · rintro ⟨h, h' | h'⟩
      · by_cases w : n = 0
        · left
          subst w
          simp
        · right
          exact h w
      · right
        exact h'
    · rintro (h | h)
      · obtain rfl := eq_zero_of_le_zero (le_of_lt_succ h)
        simp
      · exact ⟨fun _ => h, Or.inr h⟩
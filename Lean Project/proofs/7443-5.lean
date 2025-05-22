import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {n : Nat} {a' : α} {l : List α} (h : n < l.length) :
    ∃ l₁ l₂, l = l₁ ++ l[n] :: l₂ ∧ l₁.length = n ∧ l.set n a' = l₁ ++ a' :: l₂ := by
  let l₁ := l.take n
  let l₂ := (l.drop (n + 1))
  exists l₁, l₂
  constructor
  · have : l = l₁ ++ (l.drop n) := by
        rw [take_append_drop]
    rw [this]
    simp [nthLe]
    rw [drop_succ]
  · rw [length_take h]
    exact Nat.le_of_lt_succ h
  · rw [set_eq_take_drop h]
    simp

/- ACTUAL PROOF OF List.exists_of_set -/

example {n : Nat} {a' : α} {l : List α} (h : n < l.length) :
    ∃ l₁ l₂, l = l₁ ++ l[n] :: l₂ ∧ l₁.length = n ∧ l.set n a' = l₁ ++ a' :: l₂ := by
  refine ⟨l.take n, l.drop (n + 1), ⟨by simp, ⟨length_take_of_le (Nat.le_of_lt h), ?_⟩⟩⟩
  simp [set_eq_take_append_cons_drop, h]
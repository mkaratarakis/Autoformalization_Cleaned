import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat


example {n : Nat} {a' : α} {l : List α} (h : n < l.length) :
    ∃ l₁ l₂, l = l₁ ++ l[n] :: l₂ ∧ l₁.length = n ∧ l.set n a' = l₁ ++ a' :: l₂ := by
  refine ⟨l.take n, l.drop (n + 1), ⟨by simp, ⟨length_take_of_le (Nat.le_of_lt h), ?_⟩⟩⟩
  simp [set_eq_take_append_cons_drop, h]
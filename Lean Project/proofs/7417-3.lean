import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {l : List α} (h : l.drop n ≠ []) :
    (l.drop n).getLast h = l.getLast (ne_nil_of_length_pos (by simp at h; omega)) := by
  -- Simplify the hypothesis using the fact that a ≠ b is the same as ¬ (a = b)
  have h₁ : ¬ (l.drop n = []) := by simp [h]
  -- Since l.drop n ≠ [], it implies that the length of l is greater than n
  have h₂ : ¬ (length l ≤ n) := by
    intro h₃
    have h₄ : length (l.drop n) = 0 := by
      simp [h₃]
    rw [h₄] at h₁
    contradiction
  have h₅ : (l.drop n).getLast? = l.getLast? := by
    apply congrArg
    simp [getLast?, drop, h₂]
  exact Option.some.inj h₅

/- ACTUAL PROOF OF List.getLast_drop -/

example {l : List α} (h : l.drop n ≠ []) :
    (l.drop n).getLast h = l.getLast (ne_nil_of_length_pos (by simp at h; omega)) := by
  simp only [ne_eq, drop_eq_nil_iff_le] at h
  apply Option.some_inj.1
  simp only [← getLast?_eq_getLast, getLast?_drop, ite_eq_right_iff]
  omega
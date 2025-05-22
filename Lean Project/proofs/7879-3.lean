import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {l₁ l₂ : List α} {n : Nat} :
    take n (l₁ ++ l₂) = take n l₁ ++ take (n - l₁.length) l₂ := by
  induction l₁ with
  | nil =>
    simp [take, Append.append]
  | cons hd tl ih =>
    cases n with
    | zero =>
      simp [take, Append.append]
    | succ m =>
      simp [take, Append.append]
      rw [ih (n - 1)]
      simp [Nat.sub, List.length]

/- ACTUAL PROOF OF List.take_append_eq_append_take -/

example {l₁ l₂ : List α} {n : Nat} :
    take n (l₁ ++ l₂) = take n l₁ ++ take (n - l₁.length) l₂ := by
  induction l₁ generalizing n
  · simp
  · cases n
    · simp [*]
    · simp only [cons_append, take_succ_cons, length_cons, succ_eq_add_one, cons.injEq,
        append_cancel_left_eq, true_and, *]
      congr 1
      omega
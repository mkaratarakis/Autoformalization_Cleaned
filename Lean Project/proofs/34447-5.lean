import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {n} {l : List α} (h) : drop n l = get l ⟨n, h⟩ :: drop (n + 1) l := by
   rw [drop.eq_def]
   simp
   induction l generalizing n with
   | nil =>
     exfalso
     exact not_lt_zero _ h
   | cons hd tl IH =>
     cases n with
     | zero =>
       rw [Nat.zero_add]
       simp
     | succ n' =>
       rw [drop.eq_def]
       simp
       rw [IH (Nat.lt_of_succ_lt_succ h)]
       rw [Nat.succ_add]
       simp

/- ACTUAL PROOF OF List.drop_eq_get_cons -/

example {n} {l : List α} (h) : drop n l = get l ⟨n, h⟩ :: drop (n + 1) l := by
  simp [drop_eq_getElem_cons]
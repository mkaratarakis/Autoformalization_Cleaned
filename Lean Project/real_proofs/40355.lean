import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}


example (n : Nat) (a : α) : (replicate n a).length = n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [ih, replicate_succ, length_cons, Nat.succ_eq_add_one]
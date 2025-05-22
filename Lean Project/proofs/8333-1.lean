import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example (a : Nat) {b c : Nat} (h : c > a) : (a = b + c) = False := by
  intro h'
  apply Nat.noConfusion h'
  simp only [Nat.eq_iff_le_not_lt] at h'
  cases h'
  case inl h'' =>
    apply False.elim (h _ h'')
  case inr h'' =>
    apply False.elim (h _ h'')

/- ACTUAL PROOF OF Nat.Simproc.eq_add_gt -/

example (a : Nat) {b c : Nat} (h : c > a) : (a = b + c) = False := by
  rw [@Eq.comm Nat a (b + c)]
  exact add_eq_gt b h
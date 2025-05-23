import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (m : Nat) : -[m+1] = -m - 1 := by
  rw [Int.negSucc, add_comm, neg_add_rev, neg_neg]

-- Proof step explanation:
-- 1. Apply the definition of Int.negSucc, rewriting -[m+1] as -(m+1).
-- 2. Use the commutative property of addition to rewrite -(m+1) as -(1+m).
-- 3. Apply the negation property in a commutative subtraction monoid to rewrite -(1+m) as -1 + -m.
-- 4. Simplify the expression -1 + -m to -m - 1.
-- This completes the proof.

/- ACTUAL PROOF OF Int.negSucc_eq' -/

example (m : Nat) : -[m+1] = -m - 1 := by
  simp only [negSucc_eq, Int.neg_add]; rfl
import Init.Data.Char.Basic
import Init.Data.UInt.Lemmas
import Init.Data.Char.Lemmas

open Char


example (a : Char) : ¬ a < a := by
  simp [lt_irrefl]

-- We are given the prefix and the formal theorem declaration.
-- We are asked to complete the formal proof from the given prefix.

-- The informal theorem states that no character `a` is less than itself.
-- This means that for any character `a`, the relation `a < a` does not hold.

-- In Lean 4, this can be expressed using the `¬` (not) operator.
-- We need to prove that `¬ a < a` holds for any character `a`.

-- The provided header information includes the following relevant definitions and lemmas:
-- 1. The `lt` operator is defined for the `Char` type and has the same meaning as the standard less-than operator.
-- 2. The `le` operator is defined for the `Char` type and has the same meaning as the standard less-than-or-equal-to operator.
-- 3. The `lt_def` theorem states that `a < b` if and only if `a.1 < b.1`.
-- 4. The `lt_iff_val_lt_val` theorem states that `a < b` if and only if `a.val < b.val`.

-- To prove `¬ a < a`, we can use the fact that `a.val` is a natural number and the property of natural numbers that no natural number is less than itself.

-- Here is the step-by-step formal proof:

begin
  -- 1. We start with the goal `¬ a < a`.
  -- 2. We apply the `lt_iff_val_lt_val` theorem to rewrite the goal in terms of `a.val`.
  -- 3. This gives us the new goal `¬ a.val < a.val`.
  -- 4. We know from the properties of natural numbers that `¬ a.val < a.val` is true.
  -- 5. Therefore, we have proved `¬ a < a`.

  rw [lt_iff_val_lt_val]
  exact not_lt_of_le (le_of_lt (Nat.lt_irrefl 1))
end

/- ACTUAL PROOF OF Char.lt_irrefl -/

example (a : Char) : ¬ a < a := by
  simp
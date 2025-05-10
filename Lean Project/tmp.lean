import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Data.Nat.Basic

/-!
# Divisibility in groups with zero.

Lemmas about divisibility in groups and monoids with zero.

-/

assert_not_exists DenselyOrdered

variable {α : Type*}

section SemigroupWithZero

variable [SemigroupWithZero α] {a : α}

theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 :=
  Dvd.elim h fun c H' => H'.trans (zero_mul c)
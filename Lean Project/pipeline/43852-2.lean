import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.Finite

/-!

# Cardinality of finite types

The cardinality of a finite type `α` is given by `Nat.card α`. This function has
the "junk value" of `0` for infinite types, but to ensure the function has valid
output, one just needs to know that it's possible to produce a `Finite` instance
for the type. (Note: we could have defined a `Finite.card` that required you to
supply a `Finite` instance, but (a) the function would be `noncomputable` anyway
so there is no need to supply the instance and (b) the function would have a more
complicated dependent type that easily leads to "motive not type correct" errors.)

## Implementation notes

Theorems about `Nat.card` are sometimes incidentally true for both finite and infinite
types. If removing a finiteness constraint results in no loss in legibility, we remove
it. We generally put such theorems into the `SetTheory.Cardinal.Finite` module.

-/

assert_not_exists Field

noncomputable section

variable {α β γ : Type*}

/-- There is (noncomputably) an equivalence between a finite type `α` and `Fin (Nat.card α)`. -/
def Finite.equivFin (α : Type*) [Finite α] : α ≃ Fin (Nat.card α) := by
  have := (Finite.exists_equiv_fin α).choose_spec.some
  rwa [Nat.card_eq_of_equiv_fin this]

/-- Similar to `Finite.equivFin` but with control over the term used for the cardinality. -/
def Finite.equivFinOfCardEq [Finite α] {n : ℕ} (h : Nat.card α = n) : α ≃ Fin n := by
  subst h
  apply Finite.equivFin

open scoped Classical in
example (α : Type*) :
    Nat.card α = if _ : Finite α then @Fintype.card α (Fintype.ofFinite α) else 0 := by
  cases finite_or_infinite α
  · letI := Fintype.ofFinite α
    simp only [this, *, Nat.card_eq_fintype_card, dif_pos]
  · simp only [*, card_eq_zero_of_infinite, not_finite_iff_infinite.mpr, dite_false]

theorem Finite.card_pos_iff [Finite α] : 0 < Nat.card α ↔ Nonempty α := by
  haveI : Fintype α := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card]
  exact Fintype.card_pos_iff

/- ACTUAL PROOF OF Finite.card_pos_iff -/

example [Finite α] : 0 < Nat.card α ↔ Nonempty α := by
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff]
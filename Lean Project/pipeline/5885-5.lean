import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Minimal polynomials

This file defines the minimal polynomial of an element `x` of an `A`-algebra `B`,
under the assumption that x is integral over `A`, and derives some basic properties
such as irreducibility under the assumption `B` is a domain.

-/


open Polynomial Set Function

variable {A B B' : Type*}

section MinPolyDef

variable (A) [CommRing A] [Ring B] [Algebra A B]

open scoped Classical in
/-- Suppose `x : B`, where `B` is an `A`-algebra.

The minimal polynomial `minpoly A x` of `x`
is a monic polynomial with coefficients in `A` of smallest degree that has `x` as its root,
if such exists (`IsIntegral A x`) or zero otherwise.

For example, if `V` is a `𝕜`-vector space for some field `𝕜` and `f : V →ₗ[𝕜] V` then
the minimal polynomial of `f` is `minpoly 𝕜 f`.
-/
@[stacks 09GM]
noncomputable def minpoly (x : B) : A[X] :=
  if hx : IsIntegral A x then degree_lt_wf.min _ hx else 0

end MinPolyDef

namespace minpoly

section Ring

variable [CommRing A] [Ring B] [Ring B'] [Algebra A B] [Algebra A B']
variable {x : B}

/-- A minimal polynomial is monic. -/
example (hx : IsIntegral A x) : Monic (minpoly A x) := by
  delta minpoly
  rw [dif_pos hx]
  exact (degree_lt_wf.min_mem _ hx).1

/-- A minimal polynomial is nonzero. -/
theorem ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly A x ≠ 0 :=
  (monic hx).ne_zero

theorem eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0 :=
  dif_neg hx

theorem ne_zero_iff [Nontrivial A] : minpoly A x ≠ 0 ↔ IsIntegral A x :=
  ⟨fun h => of_not_not <| eq_zero.mt h, ne_zero⟩

theorem algHom_eq (f : B →ₐ[A] B') (hf : Function.Injective f) (x : B) :
    minpoly A (f x) = minpoly A x := by
  classical
  simp_rw [minpoly, isIntegral_algHom_iff _ hf, ← Polynomial.aeval_def, aeval_algHom,
    AlgHom.comp_apply, _root_.map_eq_zero_iff f hf]

theorem algebraMap_eq {B} [CommRing B] [Algebra A B] [Algebra B B'] [IsScalarTower A B B']
    (h : Function.Injective (algebraMap B B')) (x : B) :
    minpoly A (algebraMap B B' x) = minpoly A x :=
  algHom_eq (IsScalarTower.toAlgHom A B B') h x

@[simp]
theorem algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f x) = minpoly A x :=
  algHom_eq (f : B →ₐ[A] B') f.injective x

variable (A x)

/-- An element is a root of its minimal polynomial. -/
@[simp]
theorem aeval : aeval x (minpoly A x) = 0 := by
  delta minpoly
  split_ifs with hx
  · exact (degree_lt_wf.min_mem _ hx).2
  · exact aeval_zero _

/-- Given any `f : B →ₐ[A] B'` and any `x : L`, the minimal polynomial of `x` vanishes at `f x`. -/
@[simp]
theorem aeval_algHom (f : B →ₐ[A] B') (x : B) : (Polynomial.aeval (f x)) (minpoly A x) = 0 := by
  rw [Polynomial.aeval_algHom, AlgHom.coe_comp, comp_apply, aeval, map_zero]

/-- A minimal polynomial is not `1`. -/
theorem ne_one [Nontrivial B] : minpoly A x ≠ 1 := by
  intro h
  refine (one_ne_zero : (1 : B) ≠ 0) ?_
  simpa using congr_arg (Polynomial.aeval x) h

theorem map_ne_one [Nontrivial B] {R : Type*} [Semiring R] [Nontrivial R] (f : A →+* R) :
    (minpoly A x).map f ≠ 1 := by
  by_cases hx : IsIntegral A x
  · exact mt ((monic hx).eq_one_of_map_eq_one f) (ne_one A x)
  · rw [eq_zero hx, Polynomial.map_zero]
    exact zero_ne_one

/-- A minimal polynomial is not a unit. -/
theorem not_isUnit [Nontrivial B] : ¬IsUnit (minpoly A x) := by
  haveI : Nontrivial A := (algebraMap A B).domain_nontrivial
  by_cases hx : IsIntegral A x
  · exact mt (monic hx).eq_one_of_isUnit (ne_one A x)
  · rw [eq_zero hx]
    exact not_isUnit_zero

theorem mem_range_of_degree_eq_one (hx : (minpoly A x).degree = 1) :
    x ∈ (algebraMap A B).range := by
  have h : IsIntegral A x := by
    by_contra h
    rw [eq_zero h, degree_zero, ← WithBot.coe_one] at hx
    exact ne_of_lt (show ⊥ < ↑1 from WithBot.bot_lt_coe 1) hx
  have key := minpoly.aeval A x
  rw [eq_X_add_C_of_degree_eq_one hx, (minpoly.monic h).leadingCoeff, C_1, one_mul, aeval_add,
    aeval_C, aeval_X, ← eq_neg_iff_add_eq_zero, ← RingHom.map_neg] at key
  exact ⟨-(minpoly A x).coeff 0, key.symm⟩

/-- The defining property of the minimal polynomial of an element `x`:
it is the monic polynomial with smallest degree that has `x` as its root. -/
theorem min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0) :
degree (minpoly A x) ≤ degree p := by
  delta minpoly
  split_ifs with hx
  · exact (degree_lt_wf.min_mem _ hx).2
  · exact aeval_zero _
  · exact Nat.le_of_lt_succ (degree_lt_wf.min_mem _ hx)

/- ACTUAL PROOF OF minpoly.monic -/

example (hx : IsIntegral A x) : Monic (minpoly A x) := by
  delta minpoly
  rw [dif_pos hx]
  exact (degree_lt_wf.min_mem _ hx).1
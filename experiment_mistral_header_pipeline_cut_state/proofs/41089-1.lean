import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

open HasStrictDerivAt
open scoped Topology Filter ENNReal
open Filter Asymptotics Set
open ContinuousLinearMap (smulRight smulRight_one_eq_iff)
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {B : E →L[𝕜] F →L[𝕜] G} {u : 𝕜 → E} {v : 𝕜 → F} {u' : E} {v' : F}
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {c : 𝕜 → 𝕜'} {c' : 𝕜'}
variable {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
variable {𝕜' 𝔸 : Type*} [NormedField 𝕜'] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝕜'] [NormedAlgebra 𝕜 𝔸]
  {c d : 𝕜 → 𝔸} {c' d' : 𝔸} {u v : 𝕜 → 𝕜'}

example (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c y * d y) (c' * d x + c x * d') x := by
  exact hasStrictDerivAt_mul' hc hd

/-! ### Derivative of the product of two functions -/

section Mul

variable {𝔸 𝔸' : Type*} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸] [NormedAlgebra 𝕜 𝔸']
  {a b : 𝕜 → 𝔸} {a' b' : 𝔸} {c d : 𝕜 → 𝔸'} {c' d' : 𝔸'}

@[simp]
example (ha : HasDerivWithinAt a a' s x) (hb : HasDerivWithinAt b b' s x) :
    HasDerivWithinAt (fun y => a y * b y) (a x * b' + a' * b x) s x := by
  simpa only [← smulRight_one_eq_iff] using ha.mul hb

@[simp]
theorem hasDerivWithinAt_mul (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x) :
    HasDerivWithinAt (fun y => c y * d y) (c x * d' + d x * c') s x := by
  convert hc.mul' hd
  ext z
  apply mul_comm

@[simp]
theorem hasDerivAt_mul' (ha : HasDerivAt a a' x) (hb : HasDerivAt b b' x) :
    HasDerivAt (fun y => a y * b y) (a x * b' + a' * b x) x := by
  simpa only [← smulRight_one_eq_iff] using ha.mul hb

@[simp]
theorem hasDerivAt_mul (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    HasDerivAt (fun y => c y * d y) (c x * d' + d x * c') x := by
  convert hc.mul' hd
  ext z
  apply mul_comm

@[simp]
theorem hasStrictDerivAt_mul' (ha : HasStrictDerivAt a a' x) (hb : HasStrictDerivAt b b' x) :
    HasStrictDerivAt (fun y => a y * b y) (a x * b' + a' * b x) x := by
  simpa only [← smulRight_one_eq_iff] using ha.mul hb

@[simp]
theorem hasStrictDerivAt_mul (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c y * d y) (c x * d' + d x * c') x := by
  convert hc.mul' hd
  ext z
  apply mul_comm

theorem derivWithin_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : HasDerivWithinAt a a' s x)
    (hb : HasDerivWithinAt b b' s x) :
    derivWithin (a · * b) s x = a x * derivWithin b s x + derivWithin a s x * b x := by
  rw [← ha.hasDerivWithinAt.mul' hb.hasDerivWithinAt.derivWithin hxs]
  convert derivWithin_congr (fun y ↦ a x * b y + a y * b x) _ hxs
  ext; simp only [add_mul, mul_add]

theorem derivWithin_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : HasDerivWithinAt c c' s x)
    (hd : HasDerivWithinAt d d' s x) :
    derivWithin (c · * d) s x = c x * derivWithin d s x + d x * derivWithin c s x := by
  rw [← hc.hasDerivWithinAt.mul hd.hasDerivWithinAt.derivWithin hxs]
  convert derivWithin_congr (fun y ↦ c x * d y + c y * d x) _ hxs
  ext; simp only [add_mul, mul_add]

theorem deriv_mul' (ha : HasDerivAt a a' x) (hb : HasDerivAt b b' x) :
    deriv (a · * b) x = a x * deriv b x + deriv a x * b x := by
  rw [← ha.hasDerivAt.mul' hb.hasDerivAt.deriv]
  simp only [mul_add, add_mul]

theorem deriv_mul (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) :
    deriv (c · * d) x = c x * deriv d x + d x * deriv c x := by
  rw [← hc.hasDerivAt.mul hd.hasDerivAt.deriv]
  simp only [mul_add, add_mul]

@[simp]
theorem hasDerivWithinAt_mul_const' (ha : HasDerivWithinAt a a' s x) (b : 𝔸) :
    HasDerivWithinAt (fun y => a y * b) (a' * b) s x := by
  simpa only [← smulRight_one_eq_iff, mul_comm] using ha.mul hasDerivWithinAt_const

@[simp]
theorem hasDerivWithinAt_mul_const (hc : HasDerivWithinAt c c' s x) (d : 𝔸') :
    HasDerivWithinAt (fun y => c y * d) (d * c') s x := by
  simpa only [← smulRight_one_eq_iff, mul_comm] using hc.mul hasDerivWithinAt_const

@[simp]
theorem hasDerivAt_mul_const' (ha : HasDerivAt a a' x) (b : 𝔸) :
    HasDerivAt (fun y => a y * b) (a' * b) x := by
  simpa only [← smulRight_one_eq_iff, mul_comm] using ha.mul hasDerivAt_const

@[simp]
theorem hasDerivAt_mul_const (hc : HasDerivAt c c' x) (d : 𝔸') :
    HasDerivAt (fun y => c y * d) (d * c') x := by
  simpa only [← smulRight_one_eq_iff, mul_comm] using hc.mul hasDerivAt_const

@[simp]
theorem hasStrictDerivAt_mul_const' (ha : HasStrictDerivAt a a' x) (b : 𝔸) :
    HasStrictDerivAt (fun y => a y * b) (a' * b) x := by
  simpa only [← smulRight_one_eq_iff, mul_comm] using ha.mul hasStrictDerivAt_const

@[simp]
theorem hasStrictDerivAt_mul_const (hc : HasStrictDerivAt c c' x) (d : 𝔸') :
    HasStrictDerivAt (fun y => c y * d) (d * c') x := by
  simpa only [← smulRight_one_eq_iff, mul_comm] using hc.mul hasStrictDerivAt_const

theorem derivWithin_mul_const' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : HasDerivWithinAt a a' s x)
    (b : 𝔸) :
    derivWithin (fun y => a y * b) s x = derivWithin a s x * b := by
  rw [← ha.hasDerivWithinAt.mul_const' hasDerivWithinAt_const.derivWithin hxs]
  simp only [mul_comm]

theorem derivWithin_mul_const (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : HasDerivWithinAt c c' s x)
    (d : 𝔸) :
    derivWithin (fun y => c y * d) s x = d * derivWithin c s x := by
  rw [← hc.hasDerivWithinAt.mul_const hasDerivWithinAt_const.derivWithin hxs]
  simp only [mul_comm]

theorem deriv_mul_const' (ha : HasDerivAt a a' x) (b : 𝔸) :
    deriv (fun y => a y * b) x = deriv a x * b := by
  rw [← ha.hasDerivAt.mul_const' hasDerivAt_const.deriv]
  simp only [mul_comm]

theorem deriv_mul_const (hc : HasDerivAt c c' x) (d : 𝔸') :
    deriv (fun y => c y * d) x = d * deriv c x := by
  rw [← hc.hasDerivAt.mul_const hasDerivAt_const.deriv]
  simp only [mul_comm]

@[simp]
theorem hasDerivWithinAt_const_mul (ha : HasDerivWithinAt a a' s x) (b : 𝔸) :
    HasDerivWithinAt (fun y => b * a y) (b • a') s x := by
  simpa only [← smulRight_one_eq_iff, mul_comm] using hasDerivWithinAt_const.mul ha

@[simp]
theorem hasDerivAt_const_mul (ha : HasDerivAt a a' x) (b : 𝔸) :
    HasDerivAt (fun y => b * a y) (b • a') x := by
  simpa only [← smulRight_one_eq_iff, mul_comm] using hasDerivAt_const.mul ha

@[simp]
theorem hasStrictDerivAt_const_mul (ha : HasStrictDerivAt a a' x) (b : 𝔸) :
    HasStrictDerivAt (fun y => b * a y) (b • a') x := by
  simpa only [← smulRight_one_eq_iff, mul_comm] using hasStrictDerivAt_const.mul ha

theorem derivWithin_const_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : HasDerivWithinAt a a' s x)
    (b : 𝔸) :
    derivWithin (fun y => b * a y) s x = b • derivWithin a s x := by
  rw [← hasDerivWithinAt_const.mul_const ha.derivWithin hxs]
  simp only [mul_comm]

theorem deriv_const_mul (ha : HasDerivAt a a' x) (b : 𝔸) :
    deriv (fun y => b * a y) x = b • deriv a x := by
  rw [← hasDerivAt_const.mul_const ha.deriv]
  simp only [mul_comm]

end Mul

/-! ### Derivative of the product of finitely many functions -/

variable {ι : Type*} {𝔸 𝔸' : Type*} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸]
  [NormedAlgebra 𝕜 𝔸'] {u : Finset ι} {f : ι → 𝕜 → 𝔸} {f' : ι → 𝔸} {g : ι → 𝕜 → 𝔸'}
  {g' : ι → 𝔸'}

@[simp]
theorem hasDerivWithinAt_finset_prod' [DecidableEq ι] (h : ∀ i ∈ u, HasDerivWithinAt (f i) (f' i) s x) :
    HasDerivWithinAt (fun y => ∏ i ∈ u, f i y) (∑ i ∈ u, ∏ j in u.erase i, f j x * f' i) s x := by
  induction u using Finset.induction_on with
  | empty => simp [hasDerivWithinAt_const]
  | insert a s has ih =>
    simp only [Finset.prod_insert has, HasDerivWithinAt.mul, Finset.sum_insert has, ih, mul_comm]

@[simp]
theorem hasDerivWithinAt_finset_prod (h : ∀ i ∈ u, HasDerivWithinAt (g i) (g' i) s x) :
    HasDerivWithinAt (fun y => ∏ i ∈ u, g i y) (∑ i ∈ u, ∏ j in u.erase i, g j x * g' i) s x := by
  convert hasDerivWithinAt_finset_prod' h
  ext i j
  exact mul_comm _ _

@[simp]
theorem hasDerivAt_finset_prod' (h : ∀ i ∈ u, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun y => ∏ i ∈ u, f i y) (∑ i ∈ u, ∏ j in u.erase i, f j x * f' i) x := by
  simp only [← hasDerivWithinAt_univ, hasDerivWithinAt_finset_prod']

@[simp]
theorem hasDerivAt_finset_prod (h : ∀ i ∈ u, HasDerivAt (g i) (g' i) x) :
    HasDerivAt (fun y => ∏ i ∈ u, g i y) (∑ i ∈ u, ∏ j in u.erase i, g j x * g' i) x := by
  convert hasDerivAt_finset_prod' h
  ext i j
  exact mul_comm _ _

@[simp]
theorem hasStrictDerivAt_finset_prod' (h : ∀ i ∈ u, HasStrictDerivAt (f i) (f' i) x) :
    HasStrictDerivAt (fun y => ∏ i ∈ u, f i y) (∑ i ∈ u, ∏ j in u.erase i, f j x * f' i) x := by
  simp only [← hasDerivWithinAt_univ, hasDerivWithinAt_finset_prod']

@[simp]
theorem hasStrictDerivAt_finset_prod (h : ∀ i ∈ u, HasStrictDerivAt (g i) (g' i) x) :
    HasStrictDerivAt (fun y => ∏ i ∈ u, g i y) (∑ i ∈ u, ∏ j in u.erase i, g j x * g' i) x := by
  convert hasStrictDerivAt_finset_prod' h
  ext i j
  exact mul_comm _ _

theorem derivWithin_finset_prod' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, HasDerivWithinAt (f i) (f' i) s x) :
    derivWithin (fun y => ∏ i ∈ u, f i y) s x =
      ∑ i ∈ u, (∏ j ∈ u.erase i, f j x) * derivWithin (f i) s x := by
  refine' (hasDerivWithinAt_finset_prod' h).derivWithin hxs
  simp only [Finset.prod_ite_eq_single _ _ (λ _ _ _, _), Finset.prod_erase_of_not_mem,
    Finset.mem_erase, Nat.cast_id, Nat.cast_ofNat, Nat.cast_inj, ne_eq]
  rw [Finset.sum_eq_single i, add_zero]
  · simp
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_insert] at hj ⊢
    exact hj.1

theorem derivWithin_finset_prod (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, HasDerivWithinAt (g i) (g' i) s x) :
    derivWithin (fun y => ∏ i ∈ u, g i y) s x =
      ∑ i ∈ u, (∏ j ∈ u.erase i, g j x) * derivWithin (g i) s x := by
  convert derivWithin_finset_prod' hxs h
  ext i j
  exact mul_comm _ _

theorem deriv_finset_prod' (h : ∀ i ∈ u, HasDerivAt (f i) (f' i) x) :
    deriv (fun y => ∏ i ∈ u, f i y) x = ∑ i ∈ u, (∏ j ∈ u.erase i, f j x) * deriv (f i) x := by
  simp only [← derivWithin_univ, derivWithin_finset_prod']

theorem deriv_finset_prod (h : ∀ i ∈ u, HasDerivAt (g i) (g' i) x) :
    deriv (fun y => ∏ i ∈ u, g i y) x = ∑ i ∈ u, (∏ j ∈ u.erase i, g j x) * deriv (g i) x := by
  convert deriv_finset_prod' h
  ext i j
  exact mul_comm _ _

end

-- END Mathlib.Analysis.Calculus.Deriv.Mul --

-- BEGIN Mathlib.Analysis.Calculus.Deriv.Add --
/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Additive operations on derivatives

For detailed documentation of the derivative,
see the module docstring of `Analysis/Calculus/Deriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* negation
* subtraction
* addition of two functions
* multiplication of a function by a constant
* sum of finitely many functions
-/


open Filter Asymptotics Set

open ContinuousLinearMap (smulRight smulRight_one_eq_iff)

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F}
variable {f' : E →L[𝕜] F}
variable {x : E}
variable {s : Set E}
variable {L : Filter E}

section ConstSMul

variable {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]

/-! ### Derivative of a function multiplied by a constant -/

@[simp]
theorem HasDerivWithinAt.const_smul (h : HasDerivWithinAt f f' s x) (c : R) :
    HasDerivWithinAt (fun x => c • f x) (c • f') s x :=
  (c • (1 : F →L[𝕜] F)).hasDerivAt.comp_hasDerivWithinAt x h

@[simp]
theorem HasDerivAt.const_smul (h : HasDerivAt f f' x) (c : R) : HasDerivAt (fun x => c • f x) (c • f') x :=
  (c • (1 : F →L[𝕜] F)).hasDerivAt.comp_hasDerivAt x h

@[simp]
theorem HasDerivWithinAt.const_smul' (h : HasDerivWithinAt f f' s x) (c : R) :
    HasDerivWithinAt (fun x => c • f x) (f'.const_smul c) s x :=
  h.const_smul c

@[simp]
theorem HasDerivAt.const_smul' (h : HasDerivAt f f' x) (c : R) :
    HasDerivAt (fun x => c • f x) (f'.const_smul c) x :=
  h.const_smul c

@[simp]
theorem HasStrictDerivAt.const_smul (h : HasStrictDerivAt f f' x) (c : R) :
    HasStrictDerivAt (fun x => c • f x) (c • f') x :=
  (c • (1 : F →L[𝕜] F)).hasDerivAt.comp_hasStrictDerivAt x h

@[simp]
theorem HasStrictDerivAt.const_smul' (h : HasStrictDerivAt f f' x) (c : R) :
    HasStrictDerivAt (fun x => c • f x) (f'.const_smul c) x :=
  h.const_smul c

@[simp]
theorem DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    DifferentiableWithinAt 𝕜 (fun y => c • f y) s x :=
  (h.hasDerivWithinAt.const_smul c).differentiableWithinAt

@[simp]
theorem DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    DifferentiableAt 𝕜 (fun y => c • f y) x :=
  (h.hasDerivAt.const_smul c).differentiableAt

@[simp]
theorem DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) :
    DifferentiableOn 𝕜 (fun y => c • f y) s := fun x hx => (h x hx).const_smul c

@[simp]
theorem Differentiable.const_smul (h : Differentiable 𝕜 f) (c : R) :
    Differentiable 𝕜 fun y => c • f y := fun x => (h x).const_smul c

theorem derivWithin_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    derivWithin 𝕜 (fun y => c • f y) s x = c • derivWithin 𝕜 f s x :=
  (h.hasDerivWithinAt.const_smul c).derivWithin hxs

/-- Version of `derivWithin_const_smul` written with `c • f` instead of `fun y ↦ c • f y`. -/
theorem derivWithin_const_smul' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    derivWithin 𝕜 (c • f) s x = c • derivWithin 𝕜 f s x :=
  derivWithin_const_smul hxs h c

theorem deriv_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    deriv 𝕜 (fun y => c • f y) x = c • deriv 𝕜 f x :=
  (h.hasDerivAt.const_smul c).deriv

/-- Version of `deriv_const_smul` written with `c • f` instead of `fun y ↦ c • f y`. -/
theorem deriv_const_smul' (h : DifferentiableAt 𝕜 f x) (c : R) :
    deriv 𝕜 (c • f) x = c • deriv 𝕜 f x :=
  (h.hasDerivAt.const_smul c).deriv

end ConstSMul

section Neg

/-! ### Derivative of the negative of a function -/


@[simp]
theorem HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s x) : HasDerivWithinAt (fun x => -f x) (-f') s x :=
  (-1 : 𝕜 →L[𝕜] F).hasDerivAt.comp_hasDerivWithinAt x h

@[simp]
theorem HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (fun x => -f x) (-f') x :=
  (-1 : 𝕜 →L[𝕜] F).hasDerivAt.comp_hasDerivAt x h

@[simp]
theorem HasStrictDerivAt.neg (h : HasStrictDerivAt f f' x) : HasStrictDerivAt (fun x => -f x) (-f') x :=
  (-1 : 𝕜 →L[𝕜] F).hasDerivAt.comp_hasStrictDerivAt x h

@[simp]
theorem DifferentiableWithinAt.neg (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x :=
  h.hasDerivWithinAt.neg.differentiableWithinAt

@[simp]
theorem DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (fun y => -f y) x :=
  h.hasDerivAt.neg.differentiableAt

@[simp]
theorem DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (fun y => -f y) s :=
  fun x hx => (h x hx).neg

@[simp]
theorem Differentiable.neg (h : Differentiable 𝕜 f) : Differentiable 𝕜 fun y => -f y := fun x =>
  (h x).neg

theorem derivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin 𝕜 (fun y => -f y) s x = -derivWithin 𝕜 f s x := by
  classical
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact h.hasDerivWithinAt.neg.derivWithin hxs
  · rw [derivWithin_zero_of_not_differentiableWithinAt h,
      derivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    simpa

/-- Version of `derivWithin_neg` where the function is written `-f` instead of `fun y ↦ - f y`. -/
theorem derivWithin_neg' (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin 𝕜 (-f) s x = -derivWithin 𝕜 f s x :=
  derivWithin_neg hxs

@[simp]
theorem deriv_neg : deriv 𝕜 (fun y => -f y) x = -deriv 𝕜 f x := by
  simp only [← derivWithin_univ, derivWithin_neg uniqueDiffWithinAt_univ]

/-- Version of `deriv_neg` where the function is written `-f` instead of `fun y ↦ - f y`. -/
theorem deriv_neg' : deriv 𝕜 (-f) x = -deriv 𝕜 f x :=
  deriv_neg

end Neg

section Sum

/-! ### Derivative of a finite sum of functions -/

variable {ι : Type*} {A : ι → E → F} {A' : ι → E →L[𝕜] F}

@[simp]
theorem HasDerivWithinAt.sum (h : ∀ i ∈ u, HasDerivWithinAt (A i) (A' i) s x) :
    HasDerivWithinAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) s x :=
  hasDerivWithinAt_sum h

@[simp]
theorem HasDerivAt.sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x :=
  hasDerivAt_sum h

@[simp]
theorem DifferentiableWithinAt.sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    DifferentiableWithinAt 𝕜 (fun y => ∑ i ∈ u, A i y) s x :=
  HasDerivWithinAt.differentiableWithinAt <| HasDerivWithinAt.sum fun i hi => (h i hi).hasDerivWithinAt

@[simp]
theorem DifferentiableAt.sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    DifferentiableAt 𝕜 (fun y => ∑ i ∈ u, A i y) x :=
  HasDerivAt.differentiableAt <| HasDerivAt.sum fun i hi => (h i hi).hasDerivAt

@[simp]
theorem DifferentiableOn.sum (h : ∀ i ∈ u, DifferentiableOn 𝕜 (A i) s) :
    DifferentiableOn 𝕜 (fun y => ∑ i ∈ u, A i y) s := fun x hx =>
  DifferentiableWithinAt.sum fun i hi => h i hi x hx

@[simp]
theorem Differentiable.sum (h : ∀ i ∈ u, Differentiable 𝕜 (A i)) :
    Differentiable 𝕜 fun y => ∑ i ∈ u, A i y := fun x => DifferentiableAt.sum fun i hi => h i hi x

theorem derivWithin_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    derivWithin 𝕜 (fun y => ∑ i ∈ u, A i y) s x = ∑ i ∈ u, derivWithin 𝕜 (A i) s x :=
  (HasDerivWithinAt.sum fun i hi => (h i hi).hasDerivWithinAt).derivWithin hxs

theorem deriv_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    deriv 𝕜 (fun y => ∑ i ∈ u, A i y) x = ∑ i ∈ u, deriv 𝕜 (A i) x :=
  (HasDerivAt.sum fun i hi => (h i hi).hasDerivAt).deriv

end Sum

section Add

/-! ### Derivative of the sum of two functions -/

@[simp]
theorem HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x) :
    HasDerivWithinAt (fun y => f y + g y) (f' + g') s x :=
  hf.add hg

@[simp]
theorem HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x + g x) (f' + g') x :=
  hf.add hg

@[simp]
theorem DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (fun y => f y + g y) s x :=
  (hf.hasDerivWithinAt.add hg.hasDerivWithinAt).differentiableWithinAt

@[simp]
theorem DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y + g y) x :=
  (hf.hasDerivAt.add hg.hasDerivAt).differentiableAt

@[simp]
theorem DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y + g y) s := fun x hx => (hf x hx).add (hg x hx)

@[simp]
theorem Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 fun y => f y + g y := fun x => (hf x).add (hg x)

theorem derivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin 𝕜 (fun y => f y + g y) s x = derivWithin 𝕜 f s x + derivWithin 𝕜 g s x :=
  (hf.hasDerivWithinAt.add hg.hasDerivWithinAt).derivWithin hxs

/-- Version of `derivWithin_add` where the function is written as `f + g` instead
of `fun y ↦ f y + g y`. -/
theorem derivWithin_add' (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin 𝕜 (f + g) s x = derivWithin 𝕜 f s x + derivWithin 𝕜 g s x :=
  derivWithin_add hxs hf hg

theorem deriv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv 𝕜 (fun y => f y + g y) x = deriv 𝕜 f x + deriv 𝕜 g x :=
  (hf.hasDerivAt.add hg.hasDerivAt).deriv

/-- Version of `deriv_add` where the function is written as `f + g` instead
of `fun y ↦ f y + g y`. -/
theorem deriv_add' (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv 𝕜 (f + g) x = deriv 𝕜 f x + deriv 𝕜 g x :=
  deriv_add hf hg

end Add

section Sub

/-! ### Derivative of the difference of two functions -/

@[simp]
theorem HasDerivWithinAt.sub (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x) :
    HasDerivWithinAt (fun y => f y - g y) (f' - g') s x :=
  hf.sub hg

@[simp]
theorem HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x - g x) (f' - g') x :=
  hf.sub hg

@[simp]
theorem DifferentiableWithinAt.sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (fun y => f y - g y) s x :=
  (hf.hasDerivWithinAt.sub hg.hasDerivWithinAt).differentiableWithinAt

@[simp]
theorem DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y - g y) x :=
  (hf.hasDerivAt.sub hg.hasDerivAt).differentiableAt

@[simp]
theorem DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y - g y) s := fun x hx => (hf x hx).sub (hg x hx)

@[simp]
theorem Differentiable.sub (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 fun y => f y - g y := fun x => (hf x).sub (hg x)

theorem derivWithin_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin 𝕜 (fun y => f y - g y) s x = derivWithin 𝕜 f s x - derivWithin 𝕜 g s x :=
  (hf.hasDerivWithinAt.sub hg.hasDerivWithinAt).derivWithin hxs

/-- Version of `derivWithin_sub` where the function is written as `f - g` instead
of `fun y ↦ f y - g y`. -/
theorem derivWithin_sub' (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin 𝕜 (f - g) s x = derivWithin 𝕜 f s x - derivWithin 𝕜 g s x :=
  derivWithin_sub hxs hf hg

theorem deriv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv 𝕜 (fun y => f y - g y) x = deriv 𝕜 f x - deriv 𝕜 g x :=
  (hf.hasDerivAt.sub hg.hasDerivAt).deriv

/-- Version of `deriv_sub` where the function is written as `f - g` instead
of `fun y ↦ f y - g y`. -/
theorem deriv_sub' (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv 𝕜 (f - g) x = deriv 𝕜 f x - deriv 𝕜 g x :=
  deriv_sub hf hg

end Sub

end

-- END Mathlib.Analysis.Calculus.Deriv.Add --

-- BEGIN Mathlib.Analysis.Calculus.Inverse.Basic --
/-
Copyright (c) 2020 Anonymous
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Derivative of the inverse of a normed algebra element

In this file we prove formulas for `(f x)⁻¹'` and `(f x) • (g x)⁻¹'`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, multiplication, inverse
-/

universe u v w

noncomputable section

open scoped Topology Filter ENNReal

open Filter Asymptotics Set

open ContinuousLinearMap (smulRight smulRight_one_eq_iff)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f : 𝕜 → F}
variable {f' : F}
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {L : Filter 𝕜}

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {c : 𝕜 → 𝕜'} {c' : 𝕜'}
variable {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
variable {𝕜' 𝔸 : Type*} [NormedField 𝕜'] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝕜'] [NormedAlgebra 𝕜 𝔸]
  {c d : 𝕜 → 𝔸} {c' d' : 𝔸} {u v : 𝕜 → 𝕜'}

example (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c y * d y) (c' * d x + c x * d') x := by
  exact hasStrictDerivAt_mul' hc hd

-- END Mathlib.Analysis.Calculus.Inverse.Basic --

The error message is:

```
type mismatch at application
  hasStrictFDerivAt_id x
term
  x
has type
  𝕜
but is expected to have type
  E
```

The proof state before the first error is:

```
𝕜 : Type u
_inst_1 : NontriviallyNormedField 𝕜
F : Type v
_inst_2 : NormedAddCommGroup F
_inst_3 : NormedSpace 𝕜 F
E : Type w
_inst_4 : NormedAddCommGroup E
_inst_5 : NormedSpace 𝕜 E
G : Type u_1
_inst_6 : NormedAddCommGroup G
_inst_7 : NormedSpace 𝕜 G
f f₀ f₁ g : 𝕜 → F
f' f₀' f₁' g' : F
x : 𕜜
s t : Set 𝕜
L L₁ L₂ : Filter 𝕜
F : Type v
_inst_8 : NormedAddCommGroup F
_inst_9 : NormedSpace 𝕜 F
E : Type w
_inst_10 : NormedAddCommGroup E
_inst_11 : NormedSpace 𝕜 E
G : Type u_1
_inst_12 : NormedAddCommGroup G
_inst_13 : NormedSpace 𝕜 G
f f₀ f₁ g : 𝕜 → F
f' f₀' f₁' g' : F
x : 𝕜
s t : Set 𝕜
L L₁ L₂ : Filter 𝕜
F : Type v
_inst_14 : NormedAddCommGroup F
_inst_15 : NormedSpace 𝕜 F
E : Type w
_inst_16 : NormedAddCommGroup E
_inst_17 : NormedSpace 𝕜 E
G : Type u_1
_inst_18 : NormedAddCommGroup G
_inst_19 : NormedSpace 𝕜 G
f f₀ f₁ g : 𝕜 → F
f' f₀' f₁' g' : F
x : 𝕜
s t : Set 𝕜
L L₁ L₂ : Filter 𝕜
G : Type u_1
_inst_20 : NormedAddCommGroup G
_inst_21 : NormedSpace 𝕜 G
f f₀ f₁ g : 𝕜 → F
f' f₀' f₁' g' : F
x : 𝕜
s t : Set 𝕜
L L₁ L₂ : Filter 𝕜
f' f₀' f₁' g' : F
x : 𝕜
s t : Set 𝕜
L L₁ L₂ : Filter 𝕜
x : 𝕜
s t : Set 𝕜
L L₁ L₂ : Filter 𝕜
s t : Set 𝕜
L L₁ L₂ : Filter 𝕜
L L₁ L₂ : Filter 𝕜
c : 𝕜 → 𝔸
c' : 𝔸
d : 𝕜 → 𝔸
d' : 𝔸
hc : HasStrictDerivAt c c' x
hd : HasStrictDerivAt d d' x
⊢ HasStrictDerivAt (fun y => c y * d y) (c' * d x + c x * d') x
```

To proceed, we need to change the type of `x` to `E` in the prefix.

/- ACTUAL PROOF OF HasStrictDerivAt.mul -/

example (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c y * d y) (c' * d x + c x * d') x := by
  have := (HasStrictFDerivAt.mul' hc hd).hasStrictDerivAt
  rwa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul, one_smul,
    add_comm] at this
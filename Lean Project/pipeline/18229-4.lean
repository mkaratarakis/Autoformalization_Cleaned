import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Star operations on derivatives

This file contains the usual formulas (and existence assertions) for the derivative of the star
operation. Note that these only apply when the field that the derivative is respect to has a trivial
star operation; which as should be expected rules out `𝕜 = ℂ`.
-/

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : 𝕜 → F}

/-! ### Derivative of `x ↦ star x` -/


variable [StarRing 𝕜] [TrivialStar 𝕜] [StarAddMonoid F] [ContinuousStar F]
variable [StarModule 𝕜 F] {f' : F} {s : Set 𝕜} {x : 𝕜} {L : Filter 𝕜}

protected nonrec theorem HasDerivAtFilter.star (h : HasDerivAtFilter f f' x L) :
HasDerivAtFilter (fun x => star (f x)) (star f') x L := by
  rw [HasDerivAtFilter] at h
  have h₁ : HasFDerivAtFilter f (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) f') x L := h
  rw [← ContinuousLinearMap.smulRight_one_eq_iff] at h₁
  exact HasFDerivAtFilter.star h₁

/- ACTUAL PROOF OF HasDerivAtFilter.star -/

example (h : HasDerivAtFilter f f' x L) :
    HasDerivAtFilter (fun x => star (f x)) (star f') x L := by
  simpa using h.star.hasDerivAtFilter
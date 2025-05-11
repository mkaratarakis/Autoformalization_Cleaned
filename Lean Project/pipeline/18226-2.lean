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
  simpa using h.star.hasDerivAtFilter

protected nonrec theorem HasDerivWithinAt.star (h : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => star (f x)) (star f') s x :=
  h.star

protected nonrec theorem HasDerivAt.star (h : HasDerivAt f f' x) :
    HasDerivAt (fun x => star (f x)) (star f') x :=
  h.star

protected nonrec theorem HasStrictDerivAt.star (h : HasStrictDerivAt f f' x) :
HasStrictDerivAt (fun x => star (f x)) (star f') x := by
  have h_star : HasStrictFDerivAt (fun x => star (f x)) (((starL' 𝕜 : F ≃L[𝕜] F) : F →L[𝕜] F) ∘L (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) f')) x := h.star
  simpa using h_star

/- ACTUAL PROOF OF HasStrictDerivAt.star -/

example (h : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => star (f x)) (star f') x := by
  simpa using h.star.hasStrictDerivAt
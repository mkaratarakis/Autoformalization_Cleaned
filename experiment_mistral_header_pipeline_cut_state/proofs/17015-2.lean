import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Comp

open HasStrictDerivAt
open scoped Classical Topology Filter ENNReal
open Filter Asymptotics Set
open ContinuousLinearMap (smulRight smulRight_one_eq_iff)
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
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
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {s' t' : Set 𝕜'} {h : 𝕜 → 𝕜'} {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜' → 𝕜'} {h' h₂' : 𝕜'}
  {h₁' : 𝕜} {g₁ : 𝕜' → F} {g₁' : F} {L' : Filter 𝕜'} {y : 𝕜'} (x)

example (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
    intros
    rw [HasStrictDerivAt, HasFDerivAtFilter, HasFDerivAt, hasFDerivAtFilter_iff_tendsto]
    have h₁ : ContinuousLinearMap 𝕜 F 𝕜' (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (h₂' * h')) := by
      apply ContinuousLinearMap.smulRight_one_eq_iff.mpr
      have h₂ : ContinuousLinearMap 𝕜 𝕜' 𝕜' (smulRight (1 : 𝕜 →L[𝕜] 𝕜) h₂') := by
        apply ContinuousLinearMap.smulRight_one_eq_iff.mpr
        exact (smul_eq_mul h₂' 1).symm
      have h₃ : ContinuousLinearMap 𝕜 𝕜' 𝕜' (smulRight (1 : 𝕜 →L[𝕜] 𝕜) h') := by
        apply ContinuousLinearMap.smulRight_one_eq_iff.mpr
        exact (smul_eq_mul h' 1).symm
      exact ContinuousLinearMap.comp h₂ h₃
    apply HasFDerivAtFilter.comp _ _ _
    · exact hh₂
    · exact hh
    · exact Tendsto.const_nhds
    · exact h₁
    · exact ContinuousLinearMap.smulRight_one_eq_iff.mpr (smul_eq_mul _ _).symm
    exact hh₂.hasFDerivAt.hasStrictFDerivAt.hasStrictDerivAt
    exact hh.hasFDerivAt.hasStrictFDerivAt.hasStrictDerivAt
    apply HasStrictFDerivAt.comp
    apply HasStrictFDerivAt.comp
    exact hh₂.hasFDerivAt.hasStrictFDerivAt
    exact hh.hasFDerivAt.hasStrictFDerivAt
    exact Tendsto.const_nhds
    exact ContinuousLinearMap.smulRight_one_eq_iff.mpr (smul_eq_mul _ _).symm

/- ACTUAL PROOF OF HasStrictDerivAt.comp -/

example (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [mul_comm]
  exact hh₂.scomp x hh
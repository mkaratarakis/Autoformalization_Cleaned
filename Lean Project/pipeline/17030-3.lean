import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Comp

open HasDerivAtFilter
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

example (hh₂ : HasDerivAtFilter h₂ h₂' (h x) L')
    (hh : HasDerivAtFilter h h' x L) (hL : Tendsto h L L') :
    HasDerivAtFilter (h₂ ∘ h) (h₂' * h') x L := by
  apply HasDerivAtFilter.congr_of_eventuallyEq
  let g₁ := fun z => smulRight (1 : 𝕜 →L[𝕜] 𝕜) (h₂ z)
  let g₁' := smulRight (1 : 𝕜 →L[𝕜] 𝕜) h₂'
  have hg : HasDerivAtFilter g₁ g₁' (h x) L' :=
    HasFDerivAtFilter.hasDerivAtFilter
      (hh₂.hasFDerivAtFilter.restrictScalars 𝕜)
  have hf : HasDerivAtFilter h h' x L := hh
  have hL : Tendsto h L L' := hL
  have h_comm : h₂' * h' = h' • h₂' := by simp [mul_comm]
  apply h_comm.symm ▸ (HasFDerivAtFilter.hasDerivAtFilter.scomp x hg hf hL)
  rw [smulRight_one_eq_iff]

/- ACTUAL PROOF OF HasDerivAtFilter.comp -/

example (hh₂ : HasDerivAtFilter h₂ h₂' (h x) L')
    (hh : HasDerivAtFilter h h' x L) (hL : Tendsto h L L') :
    HasDerivAtFilter (h₂ ∘ h) (h₂' * h') x L := by
  rw [mul_comm]
  exact hh₂.scomp x hh hL
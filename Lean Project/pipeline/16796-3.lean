import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Add

open HasDerivAtFilter
open scoped Classical
open scoped Topology Filter ENNReal
open Asymptotics Set
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L : Filter 𝕜}
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L : Filter 𝕜}
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L : Filter 𝕜}
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L : Filter 𝕜}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L : Filter 𝕜}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L : Filter 𝕜}
variable {s t : Set 𝕜}
variable {L : Filter 𝕜}
variable {L : Filter 𝕜}

example (hf : HasDerivAtFilter f f' x L)
    (hg : HasDerivAtFilter g g' x L) : HasDerivAtFilter (fun y => f y + g y) (f' + g') x L := by
  rw [HasDerivAtFilter] at hf hg
  rw [hasFDerivAtFilter_iff_hasDerivAtFilter] at hf hg
  rw [hasFDerivAtFilter_iff_isLittleO] at hf hg
  simp only [ContinuousLinearMap.smulRight_one_eq_iff, ContinuousLinearMap.coe_smulRight] at hf hg
  have h₁ : (fun y => (f y - f x - ((y - x) • f')) + (g y - g x - ((y - x) • g'))) =o[L] fun y => y - x := by
    exact (hf.2).add (hg.2)
  have h₂ : (fun y => y - x) =o[L] fun y => y - x := by
    simp only [(· ∘ ·), id, Filter.Map.map_id, Filter.map_id', IsLittleO.of_eq, eq_self_iff_true]
  exact HasDerivAtFilter.of_isLittleO h₂ h₁

/- ACTUAL PROOF OF HasDerivAtFilter.add -/

example (hf : HasDerivAtFilter f f' x L)
    (hg : HasDerivAtFilter g g' x L) : HasDerivAtFilter (fun y => f y + g y) (f' + g') x L := by
  simpa using (hf.add hg).hasDerivAtFilter
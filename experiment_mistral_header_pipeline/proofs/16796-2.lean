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
  unfold HasDerivAtFilter at hf hg
  rw [hasFDerivAtFilter_iff_isLittleO] at hf hg
  rw [isLittleO_norm_norm] at hf hg
  rw [isLittleO_norm_norm]
  filter_upwards [hf, hg]
  rintro ε εpos
  obtain ⟨δf, hδf⟩ := hf ε εpos
  obtain ⟨δg, hδg⟩ := hg ε εpos
  refine ⟨min δf δg, fun y hy => _⟩
  rw [mem_min_sets hy] at hδf hδg
  dsimp
  rw [norm_add_le]
  apply add_lt_add
  · calc
      (‖y - x‖⁻¹ * ‖f y - f x - (ContinuousLinearMap.smulRight 1 f') (y - x)‖)
        ≤ (‖y - x‖⁻¹ * ‖f y - f x - (ContinuousLinearMap.smulRight 1 f') (y - x)‖) = ε : hδf hy
  · calc
      (‖y - x‖⁻¹ * ‖g y - g x - (ContinuousLinearMap.smulRight 1 g') (y - x)‖)
        ≤ (‖y - x‖⁻¹ * ‖g y - g x - (ContinuousLinearMap.smulRight 1 g') (y - x)‖) = ε : hδg hy

/- ACTUAL PROOF OF HasDerivAtFilter.add -/

example (hf : HasDerivAtFilter f f' x L)
    (hg : HasDerivAtFilter g g' x L) : HasDerivAtFilter (fun y => f y + g y) (f' + g') x L := by
  simpa using (hf.add hg).hasDerivAtFilter
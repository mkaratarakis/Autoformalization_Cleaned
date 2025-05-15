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
  rw [HasStrictDerivAt] at hh hh₂ ⊢
  rw [HasStrictFDerivAt] at hh hh₂ ⊢
  let f : 𝕜 → 𝕜 →L[𝕜] 𝕜' := fun y => h₂' • (h y - h x) + h₂ (h y) - h₂ (h x)
  have : ∀ᶠ y in 𝓝 x, f y = h₂' * (h y - h x) := by
    apply eventually_of_forall
    intro y
    simp [f, smul_sub, sub_smul, smul_eq_mul, mul_comm]
  rw [eventually_eq_iff_exists_mem] at this
  cases' this with V hV
  let W : Filter 𝕜 := V ⊓ 𝓝 x
  have hW : W ≤ 𝓝 x := Filter.inf_le_left
  have hW' : ∀ᶠ y in W, f y = h₂' * (h y - h x) :=
    Filter.eventually_inf.2 ⟨Filter.eventually_of_forall fun y => rfl, hV⟩
  have h_tendsto : Tendsto h W (𝓝 (h x)) :=
    Filter.Tendsto.inf hh.continuousAt (Filter.tendsto_nhds_nhds.2 hW)
  have : hh₂.isLittleO.comp_tendsto h_tendsto = this := by
    apply Filter.EventuallyEq.isLittleO_comp_tendsto
    exact hW'
  calc
    (fun y => h₂ (h y) - h₂ (h x) - (h₂' * h') • (y - x)) =ᶠ[𝓝 x] fun y => f y - (h₂' * h') • (y - x) := by
      apply Filter.eventually_eq_iff_exists_mem.1
      exact ⟨W, hW, fun y hy => by simp [hW' hy]⟩
    _ =O[𝓝 x] fun y => y - x := by
      apply hh₂.isLittleO.comp_tendsto
      exact hh.continuousAt.prod_map' hh.continuousAt
    _ =o[𝓝 x] fun y => y - x := by
      apply hh.isLittleO

  exact HasStrictFDerivAt.of_isLittleO this

/- ACTUAL PROOF OF HasStrictDerivAt.comp -/

example (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [mul_comm]
  exact hh₂.scomp x hh
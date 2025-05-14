import Mathlib.Dynamics.Flow
import Mathlib.Tactic.Monotonicity
import Mathlib.Dynamics.OmegaLimit


open Set Function Filter Topology
variable {τ : Type*} {α : Type*} {β : Type*} {ι : Type*}
variable [TopologicalSpace β]
variable (f : Filter τ) (ϕ : τ → α → β) (s s₁ s₂ : Set α)
variable (f : Filter τ) (ϕ : τ → α → β) (s s₁ s₂ : Set α)
open omegaLimit

example {m : τ → τ} {f₁ f₂ : Filter τ} (hf : Tendsto m f₁ f₂) :
    ω f₁ (fun t x ↦ ϕ (m t) x) s ⊆ ω f₂ ϕ s := by
  rw [omegaLimit_def, omegaLimit_def]
  intro y hy
  simp_rw [mem_iInter₂] at hy
  rw [mem_iInter₂]
  intro u hu
  rcases mem_map.mp (mem_of_mem_sets_of_tendsto hu hf) with ⟨v, hv, hvu⟩
  have : ∀ {w}, w ∈ v → y ∈ closure (image2 ϕ u s) := by
    intro w hw
    apply mem_closure_of_tendsto
    exact hy v hv
  exact this

/- ACTUAL PROOF OF omegaLimit_subset_of_tendsto -/

example {m : τ → τ} {f₁ f₂ : Filter τ} (hf : Tendsto m f₁ f₂) :
    ω f₁ (fun t x ↦ ϕ (m t) x) s ⊆ ω f₂ ϕ s := by
  refine iInter₂_mono' fun u hu ↦ ⟨m ⁻¹' u, tendsto_def.mp hf _ hu, ?_⟩
  rw [← image2_image_left]
  exact closure_mono (image2_subset (image_preimage_subset _ _) Subset.rfl)
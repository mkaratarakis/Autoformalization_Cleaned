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
  simp only [omegaLimit_def]
  apply iInter_mono
  rintro u hu
  have : m ⁻¹' u ∈ f₁ := mem_map.mpr (hf hu)
  rw [mem_iInter_iff] at hu
  apply hu
  apply closure_mono
  rw [image2_subset_iff]
  rintro x hx t ht
  exact ⟨m t, hx, ht⟩

/- ACTUAL PROOF OF omegaLimit_subset_of_tendsto -/

example {m : τ → τ} {f₁ f₂ : Filter τ} (hf : Tendsto m f₁ f₂) :
    ω f₁ (fun t x ↦ ϕ (m t) x) s ⊆ ω f₂ ϕ s := by
  refine iInter₂_mono' fun u hu ↦ ⟨m ⁻¹' u, tendsto_def.mp hf _ hu, ?_⟩
  rw [← image2_image_left]
  exact closure_mono (image2_subset (image_preimage_subset _ _) Subset.rfl)
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
  simp_rw [omegaLimit_def]
  intro y hy
  apply mem_Inter.2
  intro u hu
  rcases mem_closure_iff_nhds.1 (hy u hu) with ⟨v, v_open, v_nhds, yv⟩
  have : u ∈ f₂ := hf hu
  specialize yv this
  rcases yv with ⟨t, t_mem, x, x_mem, yv⟩
  exact ⟨v, v_open, v_nhds, ⟨m t, mem_of_nhds (hf v_nhds), x, x_mem, yv⟩⟩

/- ACTUAL PROOF OF omegaLimit_subset_of_tendsto -/

example {m : τ → τ} {f₁ f₂ : Filter τ} (hf : Tendsto m f₁ f₂) :
    ω f₁ (fun t x ↦ ϕ (m t) x) s ⊆ ω f₂ ϕ s := by
  refine iInter₂_mono' fun u hu ↦ ⟨m ⁻¹' u, tendsto_def.mp hf _ hu, ?_⟩
  rw [← image2_image_left]
  exact closure_mono (image2_subset (image_preimage_subset _ _) Subset.rfl)
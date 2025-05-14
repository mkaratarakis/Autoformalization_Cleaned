import Mathlib.Topology.PartialHomeomorph
import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.IsLocalHomeomorph

open IsLocalHomeomorphOn
open Topology
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : Y → Z)
  (f : X → Y) (s : Set X) (t : Set Y)
variable {g f s t}

example (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocalHomeomorphOn (g ∘ f) s := by
  intro x hx
  obtain ⟨e₁, he₁, he₁'⟩ := hg (f x) (h hx)
  obtain ⟨e₂, he₂, he₂'⟩ := hf x hx
  refine ⟨PartialHomeomorph.comp e₂ e₁, ⟨_, _⟩, _⟩
  · exact he₂
  · rw [he₁', he₂']
    apply PartialHomeomorph.comp_apply
  · rw [he₁', he₂']
    apply PartialHomeomorph.comp_symm_apply

/- ACTUAL PROOF OF IsLocalHomeomorphOn.comp -/

example (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocalHomeomorphOn (g ∘ f) s := by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩
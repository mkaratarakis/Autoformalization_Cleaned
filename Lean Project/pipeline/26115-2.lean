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
  obtain ⟨e, hxe, rfl⟩ := hf x hx
  obtain ⟨e', hxe', rfl⟩ := hg (e x) (h hx hxe)
  use e'.trans e
  constructor
  rw [e'.symm_image_eq_source_inter_preimage] at hxe'
  exact ⟨e'.symm x, hxe', mem_inter hxe' (mem_preimage.mpr (mem_image_of_mem e hxe))⟩
  ext y
  rw [e'.right_inv (mem_image_of_mem e hxe)]
  exact e.symm_apply_mem_target (mem_image_of_mem e hxe)
  rw [← e.left_inv hxe, e'.left_inv (mem_image_of_mem e hxe)]
  exact (mem_image_of_mem e hxe).2

/- ACTUAL PROOF OF IsLocalHomeomorphOn.comp -/

example (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocalHomeomorphOn (g ∘ f) s := by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩
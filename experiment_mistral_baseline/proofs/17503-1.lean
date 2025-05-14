import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Submonoid.Centralizer
import Mathlib.GroupTheory.Subgroup.Centralizer

open Subgroup
variable {G : Type*} [Group G]
variable {H K : Subgroup G}

example {g : G} {s : Set G} :
    g ∈ centralizer s ↔ ∀ h ∈ s, h * g * h⁻¹ * g⁻¹ = 1 := by
  simp only [Set.mem_setOf_eq, centralizer, id, Submonoid.mem_carrier, Submonoid.coe_mk,
    Submonoid.coe_carrier, Submonoid.coe_carrier, Submonoid.mem_carrier, Set.mem_setOf_eq,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier, Submonoid.mem_carrier,
    Submon

/- ACTUAL PROOF OF Subgroup.mem_centralizer_iff_commutator_eq_one -/

example {g : G} {s : Set G} :
    g ∈ centralizer s ↔ ∀ h ∈ s, h * g * h⁻¹ * g⁻¹ = 1 := by
  simp only [mem_centralizer_iff, mul_inv_eq_iff_eq_mul, one_mul]
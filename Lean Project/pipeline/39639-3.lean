import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Connected.PathConnected

open JoinedIn
open Topology Filter unitInterval Set Function
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*}
variable (γ : Path x y)
open ContinuousMap
variable {a₁ a₂ a₃ : X} {b₁ b₂ b₃ : Y}
variable {χ : ι → Type*} [∀ i, TopologicalSpace (χ i)] {as bs cs : ∀ i, χ i}
variable (X)
variable {X}
variable {F : Set X}

example (h : JoinedIn F x y) : x ∈ F ∧ y ∈ F := by
  obtain ⟨γ, hγ⟩ := h
  have hx : x ∈ F := by
    convert hγ 0
    exact γ.source
  have hy : y ∈ F := by
    convert hγ 1
    exact γ.target
  exact ⟨hx, hy⟩

/- ACTUAL PROOF OF JoinedIn.mem -/

example (h : JoinedIn F x y) : x ∈ F ∧ y ∈ F := by
  rcases h with ⟨γ, γ_in⟩
  have : γ 0 ∈ F ∧ γ 1 ∈ F := by constructor <;> apply γ_in
  simpa using this
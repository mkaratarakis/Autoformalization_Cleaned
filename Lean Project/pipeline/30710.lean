import Mathlib.Logic.Encodable.Lattice
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.PiSystem

open IsPiSystem
open MeasurableSpace Set
open MeasureTheory

example {α} (S : Set α) : IsPiSystem ({S} : Set (Set α)) := by
  rintro s hs t ht h_nonempty
  have hs_eq : s = S := Set.eq_of_mem_singleton hs
  have ht_eq : t = S := Set.eq_of_mem_singleton ht
  rw [hs_eq, ht_eq, inter_self]
  exact Set.mem_singleton S

/- ACTUAL PROOF OF IsPiSystem.singleton -/

example {α} (S : Set α) : IsPiSystem ({S} : Set (Set α)) := by
  intro s h_s t h_t _
  rw [Set.mem_singleton_iff.1 h_s, Set.mem_singleton_iff.1 h_t, Set.inter_self,
    Set.mem_singleton_iff]
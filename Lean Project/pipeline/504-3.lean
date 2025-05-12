import Mathlib.Order.Filter.Cofinite
import Mathlib.Topology.Bornology.Basic

open Bornology
open Set Filter
variable {ι α β : Type*}

example (t t' : Bornology α)
    (h_cobounded : @Bornology.cobounded α t = @Bornology.cobounded α t') :
    t = t' := by
  cases t
  cases t'
  congr
  · exact h_cobounded
  · apply le_cofinite_iff_compl_singleton_mem.2
    intro x
    rw [← h_cobounded]
    apply le_cofinite_iff_compl_singleton_mem.1 t_le_cofinite

/- ACTUAL PROOF OF Bornology.ext -/

example (t t' : Bornology α)
    (h_cobounded : @Bornology.cobounded α t = @Bornology.cobounded α t') :
    t = t' := by
  cases t
  cases t'
  congr
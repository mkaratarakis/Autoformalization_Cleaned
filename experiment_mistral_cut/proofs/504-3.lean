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
  dsimp at h_cobounded
  congr
  · exact h_cobounded
  · exact le_cofinite_iff_compl_singleton_mem.1 (le_cofinite'✝¹)
  · exact le_cofinite_iff_compl_singleton_mem.1 (le_cofinite'✝)

/- ACTUAL PROOF OF Bornology.ext -/

example (t t' : Bornology α)
    (h_cobounded : @Bornology.cobounded α t = @Bornology.cobounded α t') :
    t = t' := by
  cases t
  cases t'
  congr
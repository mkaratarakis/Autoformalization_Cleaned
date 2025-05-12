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
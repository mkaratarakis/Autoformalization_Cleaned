import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.FiberBundle.IsHomeomorphicTrivialBundle
import Mathlib.Analysis.Complex.ReImTopology

open TendstoUniformlyOn
open Set
open Complex Metric
variable {s t : Set ℝ}
variable {α ι : Type*}


example {f : ι → α → ℂ} {p : Filter ι} {g : α → ℂ} {K : Set α}
    (hf : TendstoUniformlyOn f g p K) :
    TendstoUniformlyOn (fun n x => (f n x).re) (fun y => (g y).re) p K := by
  apply UniformContinuous.comp_tendstoUniformlyOn uniformlyContinous_re hf
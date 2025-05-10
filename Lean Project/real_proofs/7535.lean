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
    TendstoUniformlyOn (fun n x => (f n x).im) (fun y => (g y).im) p K := by
  apply UniformContinuous.comp_tendstoUniformlyOn uniformlyContinous_im hf
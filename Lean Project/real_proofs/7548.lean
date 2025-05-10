import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.FiberBundle.IsHomeomorphicTrivialBundle
import Mathlib.Analysis.Complex.ReImTopology

open TendstoUniformly
open Set
open Complex Metric
variable {s t : Set ℝ}
variable {α ι : Type*}


example {f : ι → α → ℂ} {p : Filter ι} {g : α → ℂ}
    (hf : TendstoUniformly f g p) :
    TendstoUniformly (fun n x => (f n x).im) (fun y => (g y).im) p := by
  apply UniformContinuous.comp_tendstoUniformly uniformlyContinous_im hf
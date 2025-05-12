import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.CPolynomial

open HasFiniteFPowerSeriesAt
variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
open scoped Classical Topology
open Set Filter Asymptotics NNReal ENNReal
variable {f g : E → F} {p pf pg : FormalMultilinearSeries 𝕜 E F} {x : E} {r r' : ℝ≥0∞} {n m : ℕ}
variable (𝕜)
variable {𝕜}

example (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f + g) (pf + pg) x (max n m) := by
  rcases hf with ⟨r, hr₁⟩
  rcases hg with ⟨r', hr₂⟩
  refine ⟨min r r', _⟩
  filter_upwards [hr₁, hr₂] with _ haF haG
  simp only [Pi.add_apply, add_sub_cancel'_right]
  exact haF.add haG

/- ACTUAL PROOF OF HasFiniteFPowerSeriesAt.add -/

example (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f + g) (pf + pg) x (max n m) := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩
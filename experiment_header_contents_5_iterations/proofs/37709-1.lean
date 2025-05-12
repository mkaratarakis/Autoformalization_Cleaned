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
  -- Existence of a Common Radius
  let hr₁ := hf.hr
  let hr₂ := hg.hr

  -- Sum of Finite Formal Power Series
  have h_add : ∀ {y}, y ∈ EMetric.ball (0 : E) hr₁ → HasSum (fun k : ℕ => (pf + pg) k fun _ => y) (f (x + y) + g (x + y)),
  { intro y hy,
    have hpf := hf.hasSum hy,
    have hpg := hg.hasSum hy,
    simp only [add_apply, Pi.add_apply] at hpf hpg ⊢,
    rw [← HasSum.add hpf hpg], },

  -- Conclusion
  refine ⟨hr₁, by simp, fun y hy => _⟩,
  rw [← h_add hy],
  exact HasSum.add (hf.hasSum hy) (hg.hasSum hy),

/- ACTUAL PROOF OF HasFiniteFPowerSeriesAt.add -/

example (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f + g) (pf + pg) x (max n m) := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩
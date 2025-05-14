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
  obtain ⟨r₁, hr₁⟩ := hf
  obtain ⟨r₂, hr₂⟩ := hg
  let r := min r₁ r₂

  -- Sum of Finite Formal Power Series
  have h_add : ∀ {y}, y ∈ EMetric.ball (0 : E) r → HasSum (fun k : ℕ => (pf + pg) k fun _ => y) (f (x + y) + g (x + y)),
  { intro y hy,
    have hpf := hr₁.hasSum (EMetric.ball_subset_ball (min_le_left _ _) hy),
    have hpg := hr₂.hasSum (EMetric.ball_subset_ball (min_le_right _ _) hy),
    simp only [add_apply, Pi.add_apply] at hpf hpg ⊢,
    exact HasSum.add hpf hpg, },

  -- Conclusion
  refine ⟨r, by simp, fun y hy => _⟩,
  rw [← h_add hy],
  exact HasSum.add (hr₁.hasSum (EMetric.ball_subset_ball (min_le_left _ _) hy)) (hr₂.hasSum (EMetric.ball_subset_ball (min_le_right _ _) hy)),

/- ACTUAL PROOF OF HasFiniteFPowerSeriesAt.add -/

example (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f + g) (pf + pg) x (max n m) := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩
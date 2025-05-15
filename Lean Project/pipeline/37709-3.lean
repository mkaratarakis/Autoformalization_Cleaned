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
  -- 1. **Existence of a Common Radius:**
  rcases hf with ⟨r, hfr⟩
  rcases hg with ⟨r', hgr⟩
  use min r r'
  constructor

  -- 2. **Sum of Finite Formal Power Series:**
  constructor
  · exact ⟨
    min_le_left _ _,
    min_le_right _ _,
    fun z hz => by
      have hfr' : HasFiniteFPowerSeriesOnBall f pf x n r := hf.1
      have hgr' : HasFiniteFPowerSeriesOnBall g pg x m r' := hg.1
      have hz' : ∀ (z : E), z ∈ EMetric.ball (0 : E) (min r r') → z ∈ EMetric.ball (0 : E) r ∩ EMetric.ball (0 : E) r' := by
        simp only [EMetric.mem_ball, edist_eq_enorm_sub, norm_zero, norm_nonneg]
        intro z hz
        exact ⟨hz, hz⟩
      have hz'' : ∀ (z : E), z ∈ EMetric.ball (0 : E) (min r r') → z ∈ EMetric.ball (0 : E) r := by
        intro z hz
        exact (hz' z hz).1
      have hz''' : ∀ (z : E), z ∈ EMetric.ball (0 : E) (min r r') → z ∈ EMetric.ball (0 : E) r' := by
        intro z hz
        exact (hz' z hz).2
      have hfz : ∀ (z : E), z ∈ EMetric.ball (0 : E) (min r r') → HasSum (fun n : ℕ => pf n fun _ : Fin n => z) (f (x + z)) := by
        intro z hz
        exact hfr'.2.2 (hz'' z hz)
      have hgz : ∀ (z : E), z ∈ EMetric.ball (0 : E) (min r r') → HasSum (fun n : ℕ => pg n fun _ : Fin n => z) (g (x + z)) := by
        intro z hz
        exact hgr'.2.2 (hz''' z hz)
      have hfz_add_hgz : ∀ (z : E), z ∈ EMetric.ball (0 : E) (min r r') → HasSum (fun n : ℕ => (pf + pg) n fun _ : Fin n => z) (f (x + z) + g (x + z)) := by
        intro z hz
        apply HasSum.add
        exact hfz z hz
        exact hgz z hz
      exact hfz_add_hgz z hz⟩
  · intros m1 hm1
    simp only [Finset.sum_range_succ, Finset.sum_range_one, Pi.add_apply, Pi.zero_apply,
      add_zero, FormalMultilinearSeries.coeff_add, hfr.2.1 m1 (Nat.le_succ_of_le hm1),
      hgr.2.1 m1 (Nat.le_succ_of_le hm1)]

/- ACTUAL PROOF OF HasFiniteFPowerSeriesAt.add -/

example (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f + g) (pf + pg) x (max n m) := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩
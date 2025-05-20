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
  -- Let's denote the common radius of convergence by r.
  let r := min (HasFiniteFPowerSeriesAt.radius hf) (HasFiniteFPowerSeriesAt.radius hg)
  have hr1 : 0 < r :=
  begin
    apply lt_min,
    { apply HasFiniteFPowerSeriesAt.radius_pos, exact hf, },
    { apply HasFiniteFPowerSeriesAt.radius_pos, exact hg, },
  end
  have hr2 : 0 < r :=
  begin
    apply lt_min,
    { apply HasFiniteFPowerSeriesAt.radius_pos, exact hf, },
    { apply HasFiniteFPowerSeriesAt.radius_pos, exact hg, },
  end

  -- Define the formal finite power series for f and g.
  let pf_series := FormalMultilinearSeries.partialSum pf n
  let pg_series := FormalMultilinearSeries.partialSum pg m

  -- Define the formal finite power series for f + g.
  let pfg_series := pf_series + pg_series

  -- We need to show that the sum function f + g has a finite formal power series representation at x up to degree max n m.
  have h : ∀ y ∈ EMetric.ball x r, HasSum (fun k => (pfg_series k) fun _ => y - x) ((f + g) y) :=
  begin
    intros y hy,
    have hyf : ∀ k, 0 ≤ k → k ≤ n → (pf k) fun _ => y - x = (pf_series k) fun _ => y - x :=
    begin
      intros k hk hk',
      rw [FormalMultilinearSeries.partialSum_apply],
      simp only [Finset.sum_range_one, Finset.sum_range_succ, add_zero, Finset.mem_range],
      apply Finset.sum_eq_single_of_mem,
      { exact Finset.mem_range.mpr hk', },
      { intros k' hk'',
        simp only [Ne.def, not_false_iff, Finset.mem_range] at hk'',
        exfalso,
        apply hk,
        exact le_of_lt hk'', },
    end
    have hyg : ∀ k, 0 ≤ k → k ≤ m → (pg k) fun _ => y - x = (pg_series k) fun _ => y - x :=
    begin
      intros k hk hk',
      rw [FormalMultilinearSeries.partialSum_apply],
      simp only [Finset.sum_range_one, Finset.sum_range_succ, add_zero, Finset.mem_range],
      apply Finset.sum_eq_single_of_mem,
      { exact Finset.mem_range.mpr hk', },
      { intros k' hk'',
        simp only [Ne.def, not_false_iff, Finset.mem_range] at hk'',
        exfalso,
        apply hk,
        exact le_of_lt hk'', },
    end
    have hyfg : ∀ k, 0 ≤ k → k ≤ max n m → (pfg_series k) fun _ => y - x = (pf k + pg k) fun _ => y - x :=
    begin
      intros k hk hk',
      rw [FormalMultilinearSeries.add_apply, pi_add_apply, hyf k hk (le_max_left n m ▸ hk'), hyg k hk (le_max_right n m ▸ hk')],
    end
    have hyf_sum : HasSum (fun k => (pf k) fun _ => y - x) (f y) :=
    begin
      apply HasFiniteFPowerSeriesAt.hasSum,
      { exact hf, },
      { exact hy, },
    end
    have hyg_sum : HasSum (fun k => (pg k) fun _ => y - x) (g y) :=
    begin
      apply HasFiniteFPowerSeriesAt.hasSum,
      { exact hg, },
      { exact hy, },
    end
    have hyfg_sum : HasSum (fun k => (pfg_series k) fun _ => y - x) ((f + g) y) :=
    begin
      apply HasSum.add hyf_sum hyg_sum,
      { intros k hk,
        rw [FormalMultilinearSeries.add_apply, pi_add_apply],
        exact hyfg k hk (le_max_left n m ▸ hk), },
      { exact (add_comm _ _).symm, },
    end
    exact hyfg_sum,
  end

  -- Conclude that f + g has a finite formal power series representation at x up to degree max n m.
  exact ⟨r, hr1, hr2, h⟩

/- ACTUAL PROOF OF HasFiniteFPowerSeriesAt.add -/

example (hf : HasFiniteFPowerSeriesAt f pf x n)
    (hg : HasFiniteFPowerSeriesAt g pg x m) :
    HasFiniteFPowerSeriesAt (f + g) (pf + pg) x (max n m) := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩
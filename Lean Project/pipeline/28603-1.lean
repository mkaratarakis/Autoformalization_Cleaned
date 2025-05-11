import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Linearity of the L-series of `f` as a function of `f`

We show that the `LSeries` of `f : ℕ → ℂ` is a linear function of `f` (assuming convergence
of both L-series when adding two functions).
-/

/-!
### Addition
-/

open LSeries

lemma LSeries.term_add (f g : ℕ → ℂ) (s : ℂ) : term (f + g) s = term f s + term g s := by
  ext ⟨- | n⟩ <;>
  simp [add_div]

lemma LSeries.term_add_apply (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term (f + g) s n = term f s n + term g s n := by
  simp [term_add]

lemma LSeriesHasSum.add {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f + g) s (a + b) := by
  simpa [LSeriesHasSum, term_add] using HasSum.add hf hg

lemma LSeriesSummable.add {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f + g) s := by
  simpa [LSeriesSummable, ← term_add_apply] using Summable.add hf hg

@[simp]
lemma LSeries_add {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
    LSeries (f + g) s = LSeries f s + LSeries g s := by
  simpa [LSeries, term_add] using tsum_add hf hg

/-!
### Negation
-/

lemma LSeries.term_neg (f : ℕ → ℂ) (s : ℂ) : term (-f) s = -term f s := by
  ext ⟨- | n⟩ <;>
  simp [neg_div]

lemma LSeries.term_neg_apply (f : ℕ → ℂ) (s : ℂ) (n : ℕ) : term (-f) s n = -term f s n := by
  simp [term_neg]

lemma LSeriesHasSum.neg {f : ℕ → ℂ} {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (-f) s (-a) := by
  simpa [LSeriesHasSum, term_neg] using HasSum.neg hf

lemma LSeriesSummable.neg {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
LSeriesSummable (-f) s := by
  simp only [LSeriesSummable, LSeries.term_neg, ← neg_summable]
  exact hf

@[simp]
lemma LSeries_neg {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeries (-f) s = -LSeries f s := by
  simp only [LSeries, LSeries.term_neg, tsum_neg]
  exact hf

/- ACTUAL PROOF OF LSeriesSummable.neg -/

example {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (-f) s := by
  simpa only [LSeriesSummable, term_neg] using Summable.neg hf
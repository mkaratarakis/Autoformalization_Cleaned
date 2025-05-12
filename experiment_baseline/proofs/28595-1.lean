import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Linearity

open LSeriesHasSum
open LSeries

example {f : ℕ → ℂ} {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (-f) s (-a) := by
  rw [← neg_neg (-a)]
  rw [← LSeriesHasSum.neg_iff]
  exact hf

/- ACTUAL PROOF OF LSeriesHasSum.neg -/

example {f : ℕ → ℂ} {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (-f) s (-a) := by
  simpa only [LSeriesHasSum, term_neg] using HasSum.neg hf
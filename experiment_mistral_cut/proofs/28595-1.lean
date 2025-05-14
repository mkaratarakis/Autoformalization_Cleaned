import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Linearity

open LSeriesHasSum
open LSeries

example {f : ℕ → ℂ} {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (-f) s (-a) := by
  have h : LSeriesHasSum (-f) s (-a) := by
    simpa [LSeriesHasSum, term_neg] using hf
  exact h

/- ACTUAL PROOF OF LSeriesHasSum.neg -/

example {f : ℕ → ℂ} {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (-f) s (-a) := by
  simpa only [LSeriesHasSum, term_neg] using HasSum.neg hf
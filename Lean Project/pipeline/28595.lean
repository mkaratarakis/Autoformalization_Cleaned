import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Linearity

open LSeriesHasSum
open LSeries

example {f : ℕ → ℂ} {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (-f) s (-a) := by
  rw [LSeriesHasSum, term_neg]
  exact HasSum.neg hf

/- ACTUAL PROOF OF LSeriesHasSum.neg -/

example {f : ℕ → ℂ} {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (-f) s (-a) := by
  simpa only [LSeriesHasSum, term_neg] using HasSum.neg hf
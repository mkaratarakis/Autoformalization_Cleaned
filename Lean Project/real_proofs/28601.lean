import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Linearity

open LSeriesSummable
open LSeries


example {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f + g) s := by
  simpa only [LSeriesSummable, ← term_add_apply] using Summable.add hf hg
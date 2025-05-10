import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Multiplicative operations on derivatives

/- ACTUAL PROOF OF HasStrictFDerivAt.mul -/

example (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
    HasStrictFDerivAt (fun y => c y * d y) (c x • d' + d x • c') x := by
  convert hc.mul' hd
  ext z
  apply mul_comm
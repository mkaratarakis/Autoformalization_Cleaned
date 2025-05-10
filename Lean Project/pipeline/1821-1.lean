import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Multiplicative operations on derivatives

/- ACTUAL PROOF OF HasFDerivAt.mul -/

example (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
    HasFDerivAt (fun y => c y * d y) (c x • d' + d x • c') x := by
  convert hc.mul' hd
  ext z
  apply mul_comm
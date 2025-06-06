import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

open Complex
open Real Complex BigOperators Filter
open scoped UpperHalfPlane Topology

example (z : ℂ) :
    cot z = (Complex.exp (2 * I * z) + 1) / (I * (1 - Complex.exp (2 * I * z))) := by
  rw [cot]
  simp only [sin_eq_exp, cos_eq_exp, div_eq_mul_inv, mul_inv, mul_inv_cancel_left, mul_assoc, mul_I_I, I_mul_I, ← neg_div, ← sub_div, ← add_mul, ← mul_add, ← mul_div_assoc, ← div_div, ← div_mul_eq_div_mul_one_div]
  rw [← mul_div_assoc, ← mul_div_assoc, mul_div_assoc, mul_div_assoc]
  field_simp

/- ACTUAL PROOF OF Complex.cot_eq_exp_ratio -/

example (z : ℂ) :
    cot z = (Complex.exp (2 * I * z) + 1) / (I * (1 - Complex.exp (2 * I * z))) := by
  rw [Complex.cot, Complex.sin, Complex.cos]
  field_simp
  have h1 : exp (z * I) + exp (-(z * I)) = exp (-(z * I)) * (exp (2 * I * z) + 1) := by
    rw [mul_add, ← Complex.exp_add]
    simp only [mul_one, add_left_inj]
    ring_nf
  have h2 : (exp (-(z * I)) - exp (z * I)) * I = exp (-(z * I)) * (I * (1 - exp (2 * I * z))) := by
    ring_nf
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [h1, h2, mul_div_mul_left _ _ (Complex.exp_ne_zero _)]
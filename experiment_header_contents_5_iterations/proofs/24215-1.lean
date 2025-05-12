import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

open Complex
open Real Complex BigOperators Filter
open scoped UpperHalfPlane Topology

example (z : ℂ) :
    cot z = (Complex.exp (2 * I * z) + 1) / (I * (1 - Complex.exp (2 * I * z))) := by
  unfold cot
  rw [Complex.sin_eq_exp_sub, Complex.cos_eq_exp_add, div_eq_mul_inv]
  field_simp [mul_div_cancel_left _ (ne_of_gt (Complex.norm_exp_pos _))]
  rw [Complex.exp_neg, ←mul_assoc, ←mul_assoc, ←div_eq_mul_inv, ←sub_eq_add_neg, ←mul_sub]
  congr 2
  · simp only [mul_one, Complex.exp_add, Complex.exp_neg, neg_mul, add_neg_eq_sub, sub_eq_add_neg, Complex.exp_nat_mul, one_mul]
  · simp only [mul_one, Complex.exp_add, Complex.exp_neg, neg_mul, add_neg_eq_sub, sub_eq_add_neg, Complex.exp_nat_mul, one_mul]

  ring_nf
  simp only [Complex.exp_nat_mul, one_mul, Complex.exp_add, Complex.exp_neg, neg_mul, add_neg_eq_sub, sub_eq_add_neg]
  ring

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
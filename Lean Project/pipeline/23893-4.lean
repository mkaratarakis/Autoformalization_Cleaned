import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike


open NNReal ENNReal
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α 𝕜 : Type*} [RCLike 𝕜] {m : MeasurableSpace α} {f : α → 𝕜}
  {μ : MeasureTheory.Measure α}
variable {α 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α] {f : α → 𝕜} {μ : MeasureTheory.Measure α}

example (hre : AEMeasurable (fun x => RCLike.re (f x)) μ)
    (him : AEMeasurable (fun x => RCLike.im (f x)) μ) : AEMeasurable f μ := by
  rw [AEMeasurable] at hre him ⊢
  obtain ⟨gre, hgre, gre_eq⟩ := hre
  obtain ⟨gim, hgim, gim_eq⟩ := him
  use fun x => RCLike.ofReal (gre x) + RCLike.ofReal (gim x) * RCLike.I
  constructor
  · exact Measurable.add (RCLike.measurable_ofReal.comp hgre)
      (Measurable.mul (RCLike.measurable_ofReal.comp hgim) Measurable.const RCLike.I)
  · filter_upwards [gre_eq, gim_eq] with x hgre hgim
    show f x = RCLike.ofReal (gre x) + RCLike.ofReal (gim x) * RCLike.I
    rw [RCLike.re_add_im (f x), hgre, hgim]

/- ACTUAL PROOF OF aemeasurable_of_re_im -/

example (hre : AEMeasurable (fun x => RCLike.re (f x)) μ)
    (him : AEMeasurable (fun x => RCLike.im (f x)) μ) : AEMeasurable f μ := by
  convert AEMeasurable.add (M := 𝕜) (RCLike.measurable_ofReal.comp_aemeasurable hre)
      ((RCLike.measurable_ofReal.comp_aemeasurable him).mul_const RCLike.I)
  exact (RCLike.re_add_im _).symm
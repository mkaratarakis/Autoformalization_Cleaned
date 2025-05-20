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
  have hre' : AEMeasurable (fun x => RCLike.ofReal (RCLike.re (f x))) μ :=
    RCLike.measurable_ofReal.comp_aemeasurable hre
  have him' : AEMeasurable (fun x => RCLike.ofReal (RCLike.im (f x)) * RCLike.I) μ :=
    (RCLike.measurable_ofReal.comp_aemeasurable him).const_mul RCLike.I
  exact AEMeasurable.add hre' him'

/- ACTUAL PROOF OF aemeasurable_of_re_im -/

example (hre : AEMeasurable (fun x => RCLike.re (f x)) μ)
    (him : AEMeasurable (fun x => RCLike.im (f x)) μ) : AEMeasurable f μ := by
  convert AEMeasurable.add (M := 𝕜) (RCLike.measurable_ofReal.comp_aemeasurable hre)
      ((RCLike.measurable_ofReal.comp_aemeasurable him).mul_const RCLike.I)
  exact (RCLike.re_add_im _).symm
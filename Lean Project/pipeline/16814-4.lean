import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# One-dimensional derivatives of sums etc

In this file we prove formulas about derivatives of `f + g`, `-f`, `f - g`, and `∑ i, f i x` for
functions from the base field to a normed space over this field.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative
-/

universe u v w

open scoped Topology Filter ENNReal

open Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f g : 𝕜 → F}
variable {f' g' : F}
variable {x : 𝕜} {s : Set 𝕜} {L : Filter 𝕜}

section Add

/-! ### Derivative of the sum of two functions -/


nonrec theorem HasDerivAtFilter.add (hf : HasDerivAtFilter f f' x L)
    (hg : HasDerivAtFilter g g' x L) : HasDerivAtFilter (fun y => f y + g y) (f' + g') x L := by
  simpa using (hf.add hg).hasDerivAtFilter

nonrec theorem HasStrictDerivAt.add (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x) :
    HasStrictDerivAt (fun y => f y + g y) (f' + g') x := by simpa using (hf.add hg).hasStrictDerivAt

nonrec theorem HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s x)
    (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (fun y => f y + g y) (f' + g') s x :=
  hf.add hg

nonrec theorem HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => f x + g x) (f' + g') x :=
  hf.add hg
example (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    derivWithin (fun y => f y + g y) s x = derivWithin f s x + derivWithin g s x := by
  rcases uniqueDiffWithinAt_or_nhdsWithin_eq_bot s x with hxs | hxs
  · exact (hf.hasDerivWithinAt.add hg.hasDerivWithinAt).derivWithin hxs
  · simp [derivWithin_zero_of_isolated hxs]

@[simp]
theorem deriv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    deriv (fun y => f y + g y) x = deriv f x + deriv g x :=
  (hf.hasDerivAt.add hg.hasDerivAt).deriv

@[simp]
theorem hasDerivAtFilter_add_const_iff (c : F) :
    HasDerivAtFilter (f · + c) f' x L ↔ HasDerivAtFilter f f' x L :=
  hasFDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivAtFilter.add_const⟩ := hasDerivAtFilter_add_const_iff

@[simp]
theorem hasStrictDerivAt_add_const_iff (c : F) :
    HasStrictDerivAt (f · + c) f' x ↔ HasStrictDerivAt f f' x :=
  hasStrictFDerivAt_add_const_iff c

alias ⟨_, HasStrictDerivAt.add_const⟩ := hasStrictDerivAt_add_const_iff

@[simp]
theorem hasDerivWithinAt_add_const_iff (c : F) :
    HasDerivWithinAt (f · + c) f' s x ↔ HasDerivWithinAt f f' s x :=
  hasDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivWithinAt.add_const⟩ := hasDerivWithinAt_add_const_iff

@[simp]
theorem hasDerivAt_add_const_iff (c : F) : HasDerivAt (f · + c) f' x ↔ HasDerivAt f f' x :=
  hasDerivAtFilter_add_const_iff c

alias ⟨_, HasDerivAt.add_const⟩ := hasDerivAt_add_const_iff

theorem derivWithin_add_const (c : F) :
    derivWithin (fun y => f y + c) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_add_const]

theorem deriv_add_const (c : F) : deriv (fun y => f y + c) x = deriv f x := by
  simp only [deriv, fderiv_add_const]

@[simp]
theorem deriv_add_const' (c : F) : (deriv fun y => f y + c) = deriv f :=
  funext fun _ => deriv_add_const c

theorem hasDerivAtFilter_const_add_iff (c : F) :
    HasDerivAtFilter (c + f ·) f' x L ↔ HasDerivAtFilter f f' x L :=
  hasFDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivAtFilter.const_add⟩ := hasDerivAtFilter_const_add_iff

@[simp]
theorem hasStrictDerivAt_const_add_iff (c : F) :
    HasStrictDerivAt (c + f ·) f' x ↔  HasStrictDerivAt f f' x :=
  hasStrictFDerivAt_const_add_iff c

alias ⟨_, HasStrictDerivAt.const_add⟩ := hasStrictDerivAt_const_add_iff

@[simp]
theorem hasDerivWithinAt_const_add_iff (c : F) :
    HasDerivWithinAt (c + f ·) f' s x ↔ HasDerivWithinAt f f' s x :=
  hasDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivWithinAt.const_add⟩ := hasDerivWithinAt_const_add_iff

@[simp]
theorem hasDerivAt_const_add_iff (c : F) : HasDerivAt (c + f ·) f' x ↔ HasDerivAt f f' x :=
  hasDerivAtFilter_const_add_iff c

alias ⟨_, HasDerivAt.const_add⟩ := hasDerivAt_const_add_iff

theorem derivWithin_const_add (c : F) :
    derivWithin (c + f ·) s x = derivWithin f s x := by
  simp only [derivWithin, fderivWithin_const_add]

@[simp]
theorem derivWithin_const_add_fun (c : F) :
    derivWithin (c + f ·) = derivWithin f := by
  ext
  apply derivWithin_const_add

theorem deriv_const_add (c : F) : deriv (c + f ·) x = deriv f x := by
  simp only [deriv, fderiv_const_add]

@[simp]
theorem deriv_const_add' (c : F) : (deriv (c + f ·)) = deriv f :=
  funext fun _ => deriv_const_add c

lemma differentiableAt_comp_const_add {a b : 𝕜} :
    DifferentiableAt 𝕜 (fun x ↦ f (b + x)) a ↔ DifferentiableAt 𝕜 f (b + a) := by
  refine ⟨fun H ↦ ?_, fun H ↦ H.comp _ (differentiable_id.const_add _).differentiableAt⟩
  convert DifferentiableAt.comp (b + a) (by simpa)
    (differentiable_id.const_add (-b)).differentiableAt
  ext
  simp

lemma differentiableAt_comp_add_const {a b : 𝕜} :
    DifferentiableAt 𝕜 (fun x ↦ f (x + b)) a ↔ DifferentiableAt 𝕜 f (a + b) := by
  simpa [add_comm b] using differentiableAt_comp_const_add (f := f) (b := b)

lemma differentiableAt_iff_comp_const_add {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x ↦ f (b + x)) (-b + a) := by
  simp [differentiableAt_comp_const_add]

lemma differentiableAt_iff_comp_add_const {a b : 𝕜} :
    DifferentiableAt 𝕜 f a ↔ DifferentiableAt 𝕜 (fun x ↦ f (x + b)) (a - b) := by
  simp [differentiableAt_comp_add_const]

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/

variable {ι : Type*} {u : Finset ι} {A : ι → 𝕜 → F} {A' : ι → F}

theorem HasDerivAtFilter.sum (h : ∀ i ∈ u, HasDerivAtFilter (A i) (A' i) x L) :
    HasDerivAtFilter (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x L := by
  simpa [ContinuousLinearMap.sum_apply] using (HasFDerivAtFilter.sum h).hasDerivAtFilter

theorem HasStrictDerivAt.sum (h : ∀ i ∈ u, HasStrictDerivAt (A i) (A' i) x) :
HasStrictDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x := by
  have := HasStrictFDerivAt.sum h
  simpa only [ContinuousLinearMap.smulRight_one_eq_iff] using this

/- ACTUAL PROOF OF HasStrictDerivAt.sum -/

example (h : ∀ i ∈ u, HasStrictDerivAt (A i) (A' i) x) :
    HasStrictDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x := by
  simpa [ContinuousLinearMap.sum_apply] using (HasStrictFDerivAt.sum h).hasStrictDerivAt
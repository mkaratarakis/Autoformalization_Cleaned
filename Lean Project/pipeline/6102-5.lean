import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Additive operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* sum of finitely many functions
* multiplication of a function by a scalar constant
* negative of a function
* subtraction of two functions
-/


open Filter Asymptotics ContinuousLinearMap

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f g : E → F}
variable {f' g' : E →L[𝕜] F}
variable {x : E}
variable {s : Set E}
variable {L : Filter E}

section ConstSMul

variable {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]

/-! ### Derivative of a function multiplied by a constant -/

@[fun_prop]
example (h : HasStrictFDerivAt f f' x) (c : R) :
    HasStrictFDerivAt (fun x => c • f x) (c • f') x :=
  (c • (1 : F →L[𝕜] F)).hasStrictFDerivAt.comp x h

theorem HasFDerivAtFilter.const_smul (h : HasFDerivAtFilter f f' x L) (c : R) :
    HasFDerivAtFilter (fun x => c • f x) (c • f') x L :=
  (c • (1 : F →L[𝕜] F)).hasFDerivAtFilter.comp x h tendsto_map

@[fun_prop]
nonrec theorem HasFDerivWithinAt.const_smul (h : HasFDerivWithinAt f f' s x) (c : R) :
    HasFDerivWithinAt (fun x => c • f x) (c • f') s x :=
  h.const_smul c

@[fun_prop]
nonrec theorem HasFDerivAt.const_smul (h : HasFDerivAt f f' x) (c : R) :
    HasFDerivAt (fun x => c • f x) (c • f') x :=
  h.const_smul c

@[fun_prop]
theorem DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    DifferentiableWithinAt 𝕜 (fun y => c • f y) s x :=
  (h.hasFDerivWithinAt.const_smul c).differentiableWithinAt

@[fun_prop]
theorem DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    DifferentiableAt 𝕜 (fun y => c • f y) x :=
  (h.hasFDerivAt.const_smul c).differentiableAt

@[fun_prop]
theorem DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) :
    DifferentiableOn 𝕜 (fun y => c • f y) s := fun x hx => (h x hx).const_smul c

@[fun_prop]
theorem Differentiable.const_smul (h : Differentiable 𝕜 f) (c : R) :
    Differentiable 𝕜 fun y => c • f y := fun x => (h x).const_smul c

theorem fderivWithin_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (fun y => c • f y) s x = c • fderivWithin 𝕜 f s x :=
  (h.hasFDerivWithinAt.const_smul c).fderivWithin hxs

/-- Version of `fderivWithin_const_smul` written with `c • f` instead of `fun y ↦ c • f y`. -/
theorem fderivWithin_const_smul' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x :=
  fderivWithin_const_smul hxs h c

theorem fderiv_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (fun y => c • f y) x = c • fderiv 𝕜 f x :=
  (h.hasFDerivAt.const_smul c).fderiv

/-- Version of `fderiv_const_smul` written with `c • f` instead of `fun y ↦ c • f y`. -/
theorem fderiv_const_smul' (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (c • f) x = c • fderiv 𝕜 f x :=
  (h.hasFDerivAt.const_smul c).fderiv

end ConstSMul

section Add

/-! ### Derivative of the sum of two functions -/


@[fun_prop]
nonrec theorem HasStrictFDerivAt.add (hf : HasStrictFDerivAt f f' x)
    (hg : HasStrictFDerivAt g g' x) : HasStrictFDerivAt (fun y => f y + g y) (f' + g') x :=
   .of_isLittleO <| (hf.isLittleO.add hg.isLittleO).congr_left fun y => by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, map_sub, map_add, add_apply]
    abel

theorem HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f' x L)
    (hg : HasFDerivAtFilter g g' x L) : HasFDerivAtFilter (fun y => f y + g y) (f' + g') x L :=
  .of_isLittleO <| (hf.isLittleO.add hg.isLittleO).congr_left fun _ => by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, map_sub, map_add, add_apply]
    abel

@[fun_prop]
nonrec theorem HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (fun y => f y + g y) (f' + g') s x :=
  hf.add hg

@[fun_prop]
nonrec theorem HasFDerivAt.add (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun x => f x + g x) (f' + g') x :=
  hf.add hg

@[fun_prop]
theorem DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (fun y => f y + g y) s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y + g y) x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).differentiableAt

@[fun_prop]
theorem DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y + g y) s := fun x hx => (hf x hx).add (hg x hx)

@[simp, fun_prop]
theorem Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 fun y => f y + g y := fun x => (hf x).add (hg x)

theorem fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y + g y) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).fderivWithin hxs

/-- Version of `fderivWithin_add` where the function is written as `f + g` instead
of `fun y ↦ f y + g y`. -/
theorem fderivWithin_add' (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (f + g) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  fderivWithin_add hxs hf hg

theorem fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv

/-- Version of `fderiv_add` where the function is written as `f + g` instead
of `fun y ↦ f y + g y`. -/
theorem fderiv_add' (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (f + g) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  fderiv_add hf hg

@[simp]
theorem hasFDerivAtFilter_add_const_iff (c : F) :
    HasFDerivAtFilter (f · + c) f' x L ↔ HasFDerivAtFilter f f' x L := by
  simp [hasFDerivAtFilter_iff_isLittleOTVS]

alias ⟨_, HasFDerivAtFilter.add_const⟩ := hasFDerivAtFilter_add_const_iff

@[simp]
theorem hasStrictFDerivAt_add_const_iff (c : F) :
    HasStrictFDerivAt (f · + c) f' x ↔ HasStrictFDerivAt f f' x := by
  simp [hasStrictFDerivAt_iff_isLittleO]

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.add_const⟩ := hasStrictFDerivAt_add_const_iff

@[simp]
theorem hasFDerivWithinAt_add_const_iff (c : F) :
    HasFDerivWithinAt (f · + c) f' s x ↔ HasFDerivWithinAt f f' s x :=
  hasFDerivAtFilter_add_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.add_const⟩ := hasFDerivWithinAt_add_const_iff

@[simp]
theorem hasFDerivAt_add_const_iff (c : F) : HasFDerivAt (f · + c) f' x ↔ HasFDerivAt f f' x :=
  hasFDerivAtFilter_add_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.add_const⟩ := hasFDerivAt_add_const_iff

@[simp]
theorem differentiableWithinAt_add_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y + c) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  exists_congr fun _ ↦ hasFDerivWithinAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableWithinAt.add_const⟩ := differentiableWithinAt_add_const_iff

@[simp]
theorem differentiableAt_add_const_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => f y + c) x ↔ DifferentiableAt 𝕜 f x :=
  exists_congr fun _ ↦ hasFDerivAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableAt.add_const⟩ := differentiableAt_add_const_iff

@[simp]
theorem differentiableOn_add_const_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => f y + c) s ↔ DifferentiableOn 𝕜 f s :=
  forall₂_congr fun _ _ ↦ differentiableWithinAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableOn.add_const⟩ := differentiableOn_add_const_iff

@[simp]
theorem differentiable_add_const_iff (c : F) :
    (Differentiable 𝕜 fun y => f y + c) ↔ Differentiable 𝕜 f :=
  forall_congr' fun _ ↦ differentiableAt_add_const_iff c

@[fun_prop]
alias ⟨_,  Differentiable.add_const⟩ := differentiable_add_const_iff

@[simp]
theorem fderivWithin_add_const (c : F) :
    fderivWithin 𝕜 (fun y => f y + c) s x = fderivWithin 𝕜 f s x := by
  classical simp [fderivWithin]

@[simp]
theorem fderiv_add_const (c : F) : fderiv 𝕜 (fun y => f y + c) x = fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_add_const]

@[simp]
theorem hasFDerivAtFilter_const_add_iff (c : F) :
    HasFDerivAtFilter (c + f ·) f' x L ↔ HasFDerivAtFilter f f' x L := by
  simpa only [add_comm] using hasFDerivAtFilter_add_const_iff c

alias ⟨_, HasFDerivAtFilter.const_add⟩ := hasFDerivAtFilter_const_add_iff

@[simp]
theorem hasStrictFDerivAt_const_add_iff (c : F) :
    HasStrictFDerivAt (c + f ·) f' x ↔ HasStrictFDerivAt f f' x := by
  simpa only [add_comm] using hasStrictFDerivAt_add_const_iff c

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.const_add⟩ := hasStrictFDerivAt_const_add_iff

@[simp]
theorem hasFDerivWithinAt_const_add_iff (c : F) :
    HasFDerivWithinAt (c + f ·) f' s x ↔ HasFDerivWithinAt f f' s x :=
  hasFDerivAtFilter_const_add_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.const_add⟩ := hasFDerivWithinAt_const_add_iff

@[simp]
theorem hasFDerivAt_const_add_iff (c : F) : HasFDerivAt (c + f ·) f' x ↔ HasFDerivAt f f' x :=
  hasFDerivAtFilter_const_add_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.const_add⟩ := hasFDerivAt_const_add_iff

@[simp]
theorem differentiableWithinAt_const_add_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c + f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  exists_congr fun _ ↦ hasFDerivWithinAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableWithinAt.const_add⟩ := differentiableWithinAt_const_add_iff

@[simp]
theorem differentiableAt_const_add_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => c + f y) x ↔ DifferentiableAt 𝕜 f x :=
  exists_congr fun _ ↦ hasFDerivAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableAt.const_add⟩ := differentiableAt_const_add_iff

@[simp]
theorem differentiableOn_const_add_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => c + f y) s ↔ DifferentiableOn 𝕜 f s :=
  forall₂_congr fun _ _ ↦ differentiableWithinAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableOn.const_add⟩ := differentiableOn_const_add_iff

@[simp]
theorem differentiable_const_add_iff (c : F) :
    (Differentiable 𝕜 fun y => c + f y) ↔ Differentiable 𝕜 f :=
  forall_congr' fun _ ↦ differentiableAt_const_add_iff c

@[fun_prop]
alias ⟨_, Differentiable.const_add⟩ := differentiable_const_add_iff

@[simp]
theorem fderivWithin_const_add (c : F) :
    fderivWithin 𝕜 (fun y => c + f y) s x = fderivWithin 𝕜 f s x := by
  simpa only [add_comm] using fderivWithin_add_const c

@[simp]
theorem fderiv_const_add (c : F) : fderiv 𝕜 (fun y => c + f y) x = fderiv 𝕜 f x := by
  simp only [add_comm c, fderiv_add_const]

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


variable {ι : Type*} {u : Finset ι} {A : ι → E → F} {A' : ι → E →L[𝕜] F}

@[fun_prop]
theorem HasStrictFDerivAt.sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x := by
  simp only [hasStrictFDerivAt_iff_isLittleO] at *
  convert IsLittleO.sum h
  simp [Finset.sum_sub_distrib, ContinuousLinearMap.sum_apply]

theorem HasFDerivAtFilter.sum (h : ∀ i ∈ u, HasFDerivAtFilter (A i) (A' i) x L) :
    HasFDerivAtFilter (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x L := by
  simp only [hasFDerivAtFilter_iff_isLittleO] at *
  convert IsLittleO.sum h
  simp [ContinuousLinearMap.sum_apply]

@[fun_prop]
theorem HasFDerivWithinAt.sum (h : ∀ i ∈ u, HasFDerivWithinAt (A i) (A' i) s x) :
    HasFDerivWithinAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) s x :=
  HasFDerivAtFilter.sum h

@[fun_prop]
theorem HasFDerivAt.sum (h : ∀ i ∈ u, HasFDerivAt (A i) (A' i) x) :
    HasFDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x :=
  HasFDerivAtFilter.sum h

@[fun_prop]
theorem DifferentiableWithinAt.sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    DifferentiableWithinAt 𝕜 (fun y => ∑ i ∈ u, A i y) s x :=
  HasFDerivWithinAt.differentiableWithinAt <|
    HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    DifferentiableAt 𝕜 (fun y => ∑ i ∈ u, A i y) x :=
  HasFDerivAt.differentiableAt <| HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt

@[fun_prop]
theorem DifferentiableOn.sum (h : ∀ i ∈ u, DifferentiableOn 𝕜 (A i) s) :
    DifferentiableOn 𝕜 (fun y => ∑ i ∈ u, A i y) s := fun x hx =>
  DifferentiableWithinAt.sum fun i hi => h i hi x hx

@[simp, fun_prop]
theorem Differentiable.sum (h : ∀ i ∈ u, Differentiable 𝕜 (A i)) :
    Differentiable 𝕜 fun y => ∑ i ∈ u, A i y := fun x => DifferentiableAt.sum fun i hi => h i hi x

theorem fderivWithin_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    fderivWithin 𝕜 (fun y => ∑ i ∈ u, A i y) s x = ∑ i ∈ u, fderivWithin 𝕜 (A i) s x :=
  (HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

theorem fderiv_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    fderiv 𝕜 (fun y => ∑ i ∈ u, A i y) x = ∑ i ∈ u, fderiv 𝕜 (A i) x :=
  (HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt).fderiv

end Sum

section Neg

/-! ### Derivative of the negative of a function -/


@[fun_prop]
theorem HasStrictFDerivAt.neg (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => -f x) (-f') x :=
  (-1 : F →L[𝕜] F).hasStrictFDerivAt.comp x h

theorem HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f' x L) :
    HasFDerivAtFilter (fun x => -f x) (-f') x L :=
  (-1 : F →L[𝕜] F).hasFDerivAtFilter.comp x h tendsto_map

@[fun_prop]
nonrec theorem HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => -f x) (-f') s x :=
  h.neg

@[fun_prop]
nonrec theorem HasFDerivAt.neg (h : HasFDerivAt f f' x) : HasFDerivAt (fun x => -f x) (-f') x :=
  h.neg

@[fun_prop]
theorem DifferentiableWithinAt.neg (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x :=
  h.hasFDerivWithinAt.neg.differentiableWithinAt

@[simp]
theorem differentiableWithinAt_neg_iff :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[fun_prop]
theorem DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (fun y => -f y) x :=
  h.hasFDerivAt.neg.differentiableAt

@[simp]
theorem differentiableAt_neg_iff : DifferentiableAt 𝕜 (fun y => -f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[fun_prop]
theorem DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (fun y => -f y) s :=
  fun x hx => (h x hx).neg

@[simp]
theorem differentiableOn_neg_iff : DifferentiableOn 𝕜 (fun y => -f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[fun_prop]
theorem Differentiable.neg (h : Differentiable 𝕜 f) : Differentiable 𝕜 fun y => -f y := fun x =>
  (h x).neg

@[simp]
theorem differentiable_neg_iff : (Differentiable 𝕜 fun y => -f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

theorem fderivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => -f y) s x = -fderivWithin 𝕜 f s x := by
  classical
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact h.hasFDerivWithinAt.neg.fderivWithin hxs
  · rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    simpa

/-- Version of `fderivWithin_neg` where the function is written `-f` instead of `fun y ↦ - f y`. -/
theorem fderivWithin_neg' (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (-f) s x = -fderivWithin 𝕜 f s x :=
  fderivWithin_neg hxs

@[simp]
theorem fderiv_neg : fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_neg uniqueDiffWithinAt_univ]

/-- Version of `fderiv_neg` where the function is written `-f` instead of `fun y ↦ - f y`. -/
theorem fderiv_neg' : fderiv 𝕜 (-f) x = -fderiv 𝕜 f x :=
  fderiv_neg

end Neg

section Sub

/-! ### Derivative of the difference of two functions -/


@[fun_prop]
theorem HasStrictFDerivAt.sub (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
HasStrictFDerivAt (fun x => f x - g x) (f' - g') x := by
  have h_neg := hg.neg
  rw [sub_eq_add_neg]
  have h_add := HasStrictFDerivAt.add hf h_neg
  simp only [LinearMap.sub_apply, LinearMap.add_apply, map_sub, map_add, add_apply]
  exact h_add

/- ACTUAL PROOF OF HasStrictFDerivAt.sub -/

example (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun x => f x - g x) (f' - g') x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
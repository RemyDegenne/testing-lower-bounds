/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.MeanValue
import TestingLowerBounds.SoonInMathlib.RadonNikodym

/-!

# f-Divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

The most natural type for `f` is `ℝ≥0∞ → EReal` since we apply it to an `ℝ≥0∞`-values RN derivative,
and its value can be in general both positive or negative, and potentially +∞.
However, we use `ℝ → ℝ` instead, for the following reasons:
* domain: convexity results like `ConvexOn.map_average_le` don't work for `ℝ≥0∞` because they
  require a normed space with scalars in `ℝ`, but `ℝ≥0∞` is a module over `ℝ≥0`.
  Also, the RN derivative is almost everywhere finite for σ-finite measures, so losing ∞ in the
  domain is not an issue.
* codomain: `EReal` is underdeveloped, and all functions we will actually use are finite anyway.

Most results will require these conditions on `f`:
`(hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) (hf_one : f 1 = 0)`

## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : kernel α β} {f : ℝ → ℝ}

/-- f-Divergence of two measures, real-valued. -/
noncomputable
def fDivReal (f : ℝ → ℝ) (μ ν : Measure α) : ℝ := ∫ x, f (μ.rnDeriv ν x).toReal ∂ν

open Classical in
/-- f-Divergence of two measures, with value in `ℝ≥0∞`. Suitable for probability measures. -/
noncomputable
def fDiv (f : ℝ → ℝ) (μ ν : Measure α) : ℝ≥0∞ :=
  if Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν then ENNReal.ofReal (fDivReal f μ ν) else ∞

lemma le_fDivReal [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) :
    f (μ Set.univ).toReal ≤ fDivReal f μ ν := by
  calc f (μ Set.univ).toReal
    = f (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [Measure.integral_toReal_rnDeriv hμν]
  _ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp)
      Measure.integrable_toReal_rnDeriv hf_int
  _ = ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := rfl

lemma fDivReal_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) (hf_one : f 1 = 0)
    (hf_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) :
    0 ≤ fDivReal f μ ν :=
  calc 0 = f (μ Set.univ).toReal := by simp [hf_one]
  _ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := le_fDivReal hf_cvx hf_cont hf_int hμν

lemma fDivReal_self (hf_one : f 1 = 0) (μ : Measure α) [SigmaFinite μ] : fDivReal f μ μ = 0 := by
  have h : (fun x ↦ f (μ.rnDeriv μ x).toReal) =ᵐ[μ] 0 := by
    filter_upwards [Measure.rnDeriv_self μ] with x hx
    rw [hx, ENNReal.one_toReal, hf_one]
    rfl
  rw [fDivReal, integral_congr_ae h]
  simp

section Conditional

noncomputable
def condFDivReal (f : ℝ → ℝ) (κ η : kernel α β) (μ : Measure α) : ℝ :=
  μ[fun x ↦ fDivReal f (κ x) (η x)]

variable [MeasurableSpace.CountablyGenerated β]

section Integrable

/-! We show that the integrability of the functions used in `fDivReal f (μ ⊗ₘ κ) (μ ⊗ₘ η)`
and in `condFDivReal f κ η μ` are equivalent, when `f` is bounded from below and `μ` is finite.

TODO. -/

lemma integrable_f_rnDeriv_of_integrable_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)) :
    ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((κ a).rnDeriv (η a) x).toReal) (η a) := by
  have h := hf_int.integral_compProd
  simp only [kernel.prodMkLeft_apply, kernel.const_apply] at h
  rw [Measure.integrable_compProd_iff] at hf_int
  swap
  · exact (hf.comp_measurable (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
  have h := Measure.ae_ae_of_ae_compProd (kernel.rnDeriv_measure_compProd_right μ κ η)
  filter_upwards [h, hf_int.1] with a ha1 ha2
  refine (integrable_congr ?_).mp ha2
  filter_upwards [ha1, kernel.rnDeriv_eq_rnDeriv_measure κ η a] with b hb h_eq
  rw [hb, h_eq]

lemma integrable_fDivReal_of_integrable_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η]
    (hf_int : Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)) :
    Integrable (fun x ↦ fDivReal f (κ x) (η x)) μ := by
  have h := hf_int.integral_compProd
  simp only [kernel.prodMkLeft_apply, kernel.const_apply] at h
  have h_eq_compProd := Measure.ae_ae_of_ae_compProd (kernel.rnDeriv_measure_compProd_right μ κ η)
  refine (integrable_congr ?_).mp h
  filter_upwards [h_eq_compProd] with a ha
  rw [fDivReal]
  refine integral_congr_ae ?_
  filter_upwards [ha, kernel.rnDeriv_eq_rnDeriv_measure κ η a] with b hb h_eq
  rw [hb, h_eq]

lemma integrable_f_rnDeriv_compProd_iff [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η] (hf : StronglyMeasurable f) (hbdd : BddBelow (f '' (Set.Ici 0))) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)
      ↔ (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((κ a).rnDeriv (η a) x).toReal) (η a))
        ∧ Integrable (fun x ↦ fDivReal f (κ x) (η x)) μ := by
  have h_eq_compProd := Measure.ae_ae_of_ae_compProd (kernel.rnDeriv_measure_compProd_right μ κ η)
  have h_ae_eq : ∀ᵐ a ∂μ, (fun y ↦ f ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, y)).toReal)
      =ᵐ[η a] fun x ↦ f ((∂κ a/∂η a) x).toReal := by
    filter_upwards [h_eq_compProd] with a ha
    filter_upwards [ha, kernel.rnDeriv_eq_rnDeriv_measure κ η a] with b hb h_eq
    rw [hb, h_eq]
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
  · have h_int := h.integral_compProd
    simp only [kernel.prodMkLeft_apply, kernel.const_apply] at h_int
    rw [Measure.integrable_compProd_iff] at h
    swap
    · exact (hf.comp_measurable
        (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
    constructor
    · filter_upwards [h.1, h_ae_eq] with a ha1 ha2
      exact (integrable_congr ha2).mp ha1
    · refine (integrable_congr ?_).mp h_int
      filter_upwards [h_ae_eq] with a ha
      rw [fDivReal]
      exact integral_congr_ae ha
  · rw [Measure.integrable_compProd_iff]
    swap
    · exact (hf.comp_measurable
        (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
    constructor
    · filter_upwards [h1, h_ae_eq] with a ha1 ha2
      exact (integrable_congr ha2).mpr ha1
    · sorry

end Integrable

lemma fDivReal_compProd_left (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    (hf : StronglyMeasurable f) (hbdd : BddBelow (f '' (Set.Ici 0))) :
    fDivReal f (μ ⊗ₘ κ) (μ ⊗ₘ η) = condFDivReal f κ η μ := by
  by_cases hf_int : Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)
  swap; · sorry
  rw [condFDivReal, fDivReal]
  have h_eq : ∀ a, (fun b ↦ f (kernel.rnDeriv κ η a b).toReal)
      =ᵐ[η a] fun x ↦ f ((∂κ a/∂η a) x).toReal := by
    intro a
    filter_upwards [kernel.rnDeriv_eq_rnDeriv_measure κ η a] with b hb
    rw [hb]
  rw [Measure.integral_compProd hf_int]
  have h : ∀ᵐ a ∂μ, ∫ b, f ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b)).toReal ∂(η a)
      = ∫ b, f ((∂(κ a)/∂(η a)) b).toReal ∂(η a) := by
    filter_upwards [Measure.ae_ae_of_ae_compProd <| kernel.rnDeriv_measure_compProd_right μ κ η]
      with a ha
    refine integral_congr_ae ?_
    filter_upwards [ha, h_eq a] with b hb1 hb2
    rw [hb1, hb2]
  rw [integral_congr_ae h]
  rfl

end Conditional

end ProbabilityTheory

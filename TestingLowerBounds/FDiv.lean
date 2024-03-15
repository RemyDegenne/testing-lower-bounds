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
  {μ ν : Measure α} {κ η : kernel α β} {f g : ℝ → ℝ}

/-- f-Divergence of two measures, real-valued. -/
noncomputable
def fDivReal (f : ℝ → ℝ) (μ ν : Measure α) : ℝ := ∫ x, f (μ.rnDeriv ν x).toReal ∂ν

open Classical in
/-- f-Divergence of two measures, with value in `ℝ≥0∞`. Suitable for probability measures. -/
noncomputable
def fDiv (f : ℝ → ℝ) (μ ν : Measure α) : ℝ≥0∞ :=
  if Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν then ENNReal.ofReal (fDivReal f μ ν) else ∞

lemma fDivReal_of_not_integrable (hf : ¬ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    fDivReal f μ ν = 0 := by
  rw [fDivReal, integral_undef hf]

lemma fDivReal_const (c : ℝ) (μ ν : Measure α) :
    fDivReal (fun _ ↦ c) μ ν = (ν Set.univ).toReal * c := by
  rw [fDivReal, integral_const, smul_eq_mul]

lemma fDivReal_id [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    fDivReal id μ ν = (μ Set.univ).toReal := by
  simp only [fDivReal, id_eq, Measure.integral_toReal_rnDeriv hμν]

lemma fDivReal_id' [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    fDivReal (fun x ↦ x) μ ν = (μ Set.univ).toReal := fDivReal_id hμν

lemma fDivReal_mul (c : ℝ) (f : ℝ → ℝ) (μ ν : Measure α) :
    fDivReal (fun x ↦ c * f x) μ ν = c * fDivReal f μ ν := by
  rw [fDivReal, integral_mul_left, fDivReal]

-- TODO: in the case where both functions are convex, integrability of the sum is equivalent to
-- integrability of both, and we don't need hf and hg.
lemma fDivReal_add (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (hg : Integrable (fun x ↦ g ((∂μ/∂ν) x).toReal) ν) :
    fDivReal (fun x ↦ f x + g x) μ ν = fDivReal f μ ν + fDivReal g μ ν := by
  rw [fDivReal, integral_add hf hg, fDivReal, fDivReal]

-- TODO: in the case where both functions are convex, integrability of the sum is equivalent to
-- integrability of both, and we don't need hf and hg.
lemma fDivReal_sub (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (hg : Integrable (fun x ↦ g ((∂μ/∂ν) x).toReal) ν) :
    fDivReal (fun x ↦ f x - g x) μ ν = fDivReal f μ ν - fDivReal g μ ν := by
  rw [fDivReal, integral_sub hf hg, fDivReal, fDivReal]

lemma fDivReal_withDensity_rnDeriv (μ ν : Measure α) [SigmaFinite ν] :
    fDivReal f (ν.withDensity (∂μ/∂ν)) ν = fDivReal f μ ν := by
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity ν (Measure.measurable_rnDeriv μ ν)] with a ha
  rw [ha]

lemma fDivReal_add_linear' (c : ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDivReal (fun x ↦ f x + c * (x - 1)) μ ν
      = fDivReal f μ ν + c * ((μ Set.univ).toReal - (ν Set.univ).toReal) := by
  rw [fDivReal_add hf]
  · rw [fDivReal_mul, fDivReal_sub Measure.integrable_toReal_rnDeriv (integrable_const _),
      fDivReal_const, fDivReal_id' hμν, mul_one]
  · exact (Measure.integrable_toReal_rnDeriv.sub (integrable_const _)).const_mul c

lemma fDivReal_add_linear (c : ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (h_eq : μ Set.univ = ν Set.univ) :
    fDivReal (fun x ↦ f x + c * (x - 1)) μ ν = fDivReal f μ ν := by
  by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDivReal_add_linear' c hμν hf, h_eq, sub_self, mul_zero, add_zero]
  · rw [fDivReal_of_not_integrable hf,fDivReal_of_not_integrable]
    refine fun h_int ↦ hf ?_
    have : (fun x ↦ f ((∂μ/∂ν) x).toReal)
        = fun x ↦ (f ((∂μ/∂ν) x).toReal + c * (((∂μ/∂ν) x).toReal - 1))
          - c * (((∂μ/∂ν) x).toReal - 1) := by
      ext x
      simp
    rw [this]
    exact h_int.add ((Measure.integrable_toReal_rnDeriv.sub (integrable_const _)).const_mul c).neg

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

open Classical in
/- Conditinal f-divergence.

We enforce `∀ᵐ a ∂μ, Integrable (fun x ↦ f ((κ a).rnDeriv (η a) x).toReal) (η a)`, to ensure
that `condFDivReal f κ η μ` and `fDivReal f (μ ⊗ₘ κ) (μ ⊗ₘ η)` are well defined under the same
conditions (these two quantities are then always equal). -/
noncomputable
def condFDivReal (f : ℝ → ℝ) (κ η : kernel α β) (μ : Measure α) : ℝ :=
  if ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((κ a).rnDeriv (η a) x).toReal) (η a)
  then μ[fun x ↦ fDivReal f (κ x) (η x)]
  else 0

lemma condFDivReal_of_not_ae_integrable
    (hf : ¬ ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((κ a).rnDeriv (η a) x).toReal) (η a)) :
    condFDivReal f κ η μ = 0 := by
  rw [condFDivReal, if_neg hf]

lemma condFDivReal_eq
    (hf : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((κ a).rnDeriv (η a) x).toReal) (η a)) :
    condFDivReal f κ η μ = μ[fun x ↦ fDivReal f (κ x) (η x)] :=
  if_pos hf

lemma condFDivReal_of_not_integrable (hf : ¬ Integrable (fun x ↦ fDivReal f (κ x) (η x)) μ) :
    condFDivReal f κ η μ = 0 := by
  by_cases hf' : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((κ a).rnDeriv (η a) x).toReal) (η a)
  · rw [condFDivReal, if_pos hf', integral_undef hf]
  · exact condFDivReal_of_not_ae_integrable hf'

variable [MeasurableSpace.CountablyGenerated β]

section Integrable

/-! We show that the integrability of the functions used in `fDivReal f (μ ⊗ₘ κ) (μ ⊗ₘ η)`
and in `condFDivReal f κ η μ` are equivalent. -/

-- todo find better name
theorem _root_.MeasureTheory.Integrable.compProd_mk_left_ae' [NormedAddCommGroup E]
    [IsFiniteMeasure μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ ⊗ₘ κ)) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ f (x, y)) (κ x) :=
  hf.compProd_mk_left_ae

theorem _root_.MeasureTheory.Integrable.integral_norm_compProd' [NormedAddCommGroup E]
    [IsFiniteMeasure μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun x ↦ ∫ y, ‖f (x, y)‖ ∂(κ x)) μ :=
  hf.integral_norm_compProd

theorem _root_.MeasureTheory.Integrable.integral_compProd' [NormedAddCommGroup E]
    [IsFiniteMeasure μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄ [NormedSpace ℝ E] [CompleteSpace E]
    (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun x ↦ ∫ y, f (x, y) ∂(κ x)) μ :=
  hf.integral_compProd

lemma integrable_f_rnDeriv_of_integrable_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)) :
    ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((κ a).rnDeriv (η a) x).toReal) (η a) := by
  have h := hf_int.integral_compProd'
  rw [Measure.integrable_compProd_iff] at hf_int
  swap
  · exact (hf.comp_measurable (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
  have h := kernel.rnDeriv_measure_compProd_right' μ κ η
  filter_upwards [h, hf_int.1] with a ha1 ha2
  refine (integrable_congr ?_).mp ha2
  filter_upwards [ha1] with b hb
  rw [hb]

lemma integrable_fDivReal_of_integrable_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η]
    (hf_int : Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)) :
    Integrable (fun x ↦ fDivReal f (κ x) (η x)) μ := by
  have h := hf_int.integral_compProd
  simp only [kernel.prodMkLeft_apply, kernel.const_apply] at h
  have h_eq_compProd := kernel.rnDeriv_measure_compProd_right' μ κ η
  refine (integrable_congr ?_).mp h
  filter_upwards [h_eq_compProd] with a ha
  rw [fDivReal]
  refine integral_congr_ae ?_
  filter_upwards [ha] with b hb
  rw [hb]

lemma f_compProd_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂ν, (fun b ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal)
      =ᵐ[η a] fun b ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal := by
  have h_eq_compProd := kernel.rnDeriv_measure_compProd' μ ν κ η
  filter_upwards [h_eq_compProd] with a ha
  filter_upwards [ha] with b hb
  rw [hb]

lemma integral_f_compProd_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a))
      =ᵐ[ν] fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a) := by
  filter_upwards [f_compProd_congr μ ν κ η] with a ha using integral_congr_ae ha

lemma integral_f_compProd_right_congr (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b)).toReal ∂(η a))
      =ᵐ[μ] fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a) := by
  filter_upwards [integral_f_compProd_congr μ μ κ η, Measure.rnDeriv_self μ] with a ha h_eq_one
  rw [ha]
  simp_rw [h_eq_one, one_mul]

lemma integrable_f_rnDeriv_compProd_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η)
      ↔ (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a)) ν := by
  have h_ae_eq : ∀ᵐ a ∂ν, (fun y ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, y)).toReal)
      =ᵐ[η a] fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal := f_compProd_congr μ ν κ η
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
  · have h_int := h.integral_compProd'
    rw [Measure.integrable_compProd_iff] at h
    swap
    · exact (hf.comp_measurable
        (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
    constructor
    · filter_upwards [h.1, h_ae_eq] with a ha1 ha2
      exact (integrable_congr ha2).mp ha1
    · refine (integrable_congr ?_).mp h_int
      filter_upwards [h_ae_eq] with a ha
      exact integral_congr_ae ha
  · rw [Measure.integrable_compProd_iff]
    swap
    · exact (hf.comp_measurable
        (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
    constructor
    · filter_upwards [h1, h_ae_eq] with a ha1 ha2
      exact (integrable_congr ha2).mpr ha1
    · rw [← integrable_congr (integral_f_compProd_congr μ ν κ η)] at h2
      -- todo: cut into two parts, depending on sign of f.
      -- on the positive part, use h2.
      -- on the negative part, use `f x ≥ a * x + b` by convexity, then since both measures are
      -- finite the integral is finite.
      sorry

lemma integrable_f_rnDeriv_compProd_right_iff [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η] (hf : StronglyMeasurable f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)
      ↔ (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((κ a).rnDeriv (η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ fDivReal f (κ a) (η a)) μ := by
  rw [integrable_f_rnDeriv_compProd_iff hf]
  have h_self : ∂μ/∂μ =ᵐ[μ] fun _ ↦ 1 := Measure.rnDeriv_self μ
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩⟩
  · filter_upwards [h_self, h1] with a h_eq_one ha
    simp_rw [h_eq_one, one_mul] at ha
    exact ha
  · refine (integrable_congr ?_).mpr h2
    filter_upwards [h_self] with a ha
    simp_rw [ha, one_mul]
    rfl
  · filter_upwards [h_self, h1] with a h_eq_one ha
    simp_rw [h_eq_one, one_mul]
    exact ha
  · refine (integrable_congr ?_).mpr h2
    filter_upwards [h_self] with a ha
    simp_rw [ha, one_mul]
    rfl

end Integrable

lemma fDivReal_compProd_left (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f) :
    fDivReal f (μ ⊗ₘ κ) (μ ⊗ₘ η) = condFDivReal f κ η μ := by
  by_cases hf_int : Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)
  swap
  · rw [fDivReal_of_not_integrable hf_int]
    rw [integrable_f_rnDeriv_compProd_right_iff hf] at hf_int
    push_neg at hf_int
    by_cases hf_int' : ∀ᵐ (a : α) ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a)
    · rw [condFDivReal_of_not_integrable (hf_int hf_int')]
    · rw [condFDivReal_of_not_ae_integrable hf_int']
  have hf_int' := (integrable_f_rnDeriv_compProd_right_iff hf).mp hf_int
  rw [condFDivReal_eq hf_int'.1, fDivReal, Measure.integral_compProd hf_int]
  rw [integral_congr_ae (integral_f_compProd_right_congr μ κ η)]
  rfl

lemma fDivReal_compProd_withDensity_rnDeriv (μ ν : Measure α) (κ η : kernel α β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    fDivReal f ((ν.withDensity (∂μ/∂ν)) ⊗ₘ (kernel.withDensity η (kernel.rnDeriv κ η))) (ν ⊗ₘ η)
      = fDivReal f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  refine integral_congr_ae ?_
  filter_upwards [kernel.todo1 μ ν κ η] with p hp
  rw [hp]

lemma condFDivReal_withDensity_rnDeriv (κ η : kernel α β) (μ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDivReal f (kernel.withDensity η (kernel.rnDeriv κ η)) η μ = condFDivReal f κ η μ := by
  sorry

end Conditional

lemma fDivReal_compProd_right [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : kernel α β) [IsMarkovKernel κ] (hf : StronglyMeasurable f) :
    fDivReal f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = fDivReal f μ ν := by
  have h_compProd := kernel.rnDeriv_measure_compProd_left μ ν κ
  by_cases hf_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ κ) p).toReal) (ν ⊗ₘ κ)
  swap
  · rw [fDivReal_of_not_integrable hf_int, fDivReal_of_not_integrable]
    have hf_int' : ¬ Integrable (fun p ↦ f ((∂μ/∂ν) p.1).toReal) (ν ⊗ₘ κ) := by
      refine fun h_not ↦ hf_int ((integrable_congr ?_).mpr h_not)
      filter_upwards [h_compProd] with p hp
      rw [hp]
    rw [Measure.integrable_compProd_iff] at hf_int'
    swap
    · exact (hf.comp_measurable ((Measure.measurable_rnDeriv _ _).comp
        measurable_fst).ennreal_toReal).aestronglyMeasurable
    push_neg at hf_int'
    simp only [integrable_const, Filter.eventually_true, norm_eq_abs, integral_const, measure_univ,
      ENNReal.one_toReal, smul_eq_mul, one_mul, forall_true_left] at hf_int'
    sorry
  rw [fDivReal, Measure.integral_compProd hf_int]
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_compProd h_compProd] with a ha
  have : ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ κ) (a, b)).toReal ∂κ a = ∫ b, f ((∂μ/∂ν) a).toReal ∂κ a := by
    refine integral_congr_ae ?_
    filter_upwards [ha] with b hb
    rw [hb]
  simp [this, integral_const]

lemma f_rnDeriv_ae_le_integral [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf : StronglyMeasurable f)
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂ν, κ a ≪ η a) :
    (fun a ↦ f ((∂μ/∂ν) a).toReal)
      ≤ᵐ[ν] fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a) := by
  have h_compProd := kernel.rnDeriv_measure_compProd' μ ν κ η
  have h_lt_top := Measure.ae_ae_of_ae_compProd <| Measure.rnDeriv_lt_top (μ ⊗ₘ κ) (ν ⊗ₘ η)
  filter_upwards [hκη, h_compProd, h_lt_top] with a h_ac h_eq h_lt_top
  calc f ((∂μ/∂ν) a).toReal
    = f ((∂μ/∂ν) a * κ a Set.univ).toReal  := by simp
  _ = f ((∂μ/∂ν) a * ∫⁻ b, (∂κ a/∂η a) b ∂η a).toReal := by rw [Measure.lintegral_rnDeriv h_ac]
  _ = f (∫⁻ b,(∂μ/∂ν) a * (∂κ a/∂η a) b ∂η a).toReal := by
        rw [lintegral_const_mul _ (Measure.measurable_rnDeriv _ _)]
  _ = f (∫⁻ b, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b) ∂η a).toReal := by rw [lintegral_congr_ae h_eq]
  _ = f (∫ b, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a) := by
        rw [integral_toReal _ h_lt_top]
        exact ((Measure.measurable_rnDeriv _ _).comp measurable_prod_mk_left).aemeasurable
  _ ≤ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a := by
        rw [← average_eq_integral, ← average_eq_integral]
        rw [integrable_f_rnDeriv_compProd_iff hf] at h_int
        refine ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp) ?_ ?_
        · sorry  -- Integrable (fun x ↦ ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, x)).toReal) (η a)
        · sorry  -- Integrable (fun x ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, x)).toReal) (η a)

lemma le_fDivReal_compProd_aux [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf : StronglyMeasurable f)
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (h_int_meas : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂ν, κ a ≪ η a) :
    fDivReal f μ ν ≤ fDivReal f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  rw [fDivReal, fDivReal, Measure.integral_compProd h_int]
  refine integral_mono_ae ?_ ?_ ?_
  · exact h_int_meas
  · sorry -- Integrable (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a) ν
  exact f_rnDeriv_ae_le_integral μ ν κ η hf_cvx hf_cont hf h_int hμν hκη

lemma le_fDivReal_compProd [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (h_int_meas : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDivReal f μ ν ≤ fDivReal f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  sorry

end ProbabilityTheory

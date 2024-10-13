/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.CompProd

/-!

# f-Divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open MeasureTheory MeasurableSpace

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : ℝ → ℝ}

section IntegralRnDeriv

-- todo name
lemma lintegral_measure_prod_mk_left {f : α → Set β → ℝ≥0∞} (hf : ∀ a, f a ∅ = 0)
    {s : Set α} (hs : MeasurableSet s) (t : Set β) :
    ∫⁻ a, f a (Prod.mk a ⁻¹' s ×ˢ t) ∂μ = ∫⁻ a in s, f a t ∂μ := by
  rw [← lintegral_indicator _ hs]
  congr with a
  classical
  rw [Set.indicator_apply]
  split_ifs with ha <;> simp [ha, hf]

variable [CountableOrCountablyGenerated α β]

lemma setLIntegral_rnDeriv_mul_withDensity
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a in s, (∂μ/∂ν) a * η.withDensity (κ.rnDeriv η) a t ∂ν
      = (ν ⊗ₘ η).withDensity (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (s ×ˢ t) := by
  have : ∀ a, η.withDensity (κ.rnDeriv η) a t = ∫⁻ y in t, κ.rnDeriv η a y ∂(η a) := by
    intro a
    rw [Kernel.withDensity_apply']
    exact κ.measurable_rnDeriv _
  simp_rw [this]
  rw [withDensity_apply _ (hs.prod ht),
    Measure.setLIntegral_compProd (Measure.measurable_rnDeriv _ _) hs ht]
  refine setLIntegral_congr_fun hs ?_
  filter_upwards [κ.rnDeriv_measure_compProd' μ ν η] with a ha _
  rw [← lintegral_const_mul _ (κ.measurable_rnDeriv_right _ _)]
  refine setLIntegral_congr_fun ht ?_
  filter_upwards [ha, κ.rnDeriv_eq_rnDeriv_measure] with b hb hb' _
  rw [hb, hb']

lemma lintegral_rnDeriv_mul_withDensity (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a, (∂μ/∂ν) a * η.withDensity (κ.rnDeriv η) a t ∂ν
      = (ν ⊗ₘ η).withDensity (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (.univ ×ˢ t) := by
  rw [← setLIntegral_rnDeriv_mul_withDensity _ _ _ _ .univ ht, setLIntegral_univ]

lemma setLIntegral_rnDeriv_mul_singularPart
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a in s, (∂μ/∂ν) a * (κ a).singularPart (η a) t ∂ν
      = ((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) (s ×ˢ t) := by
  rw [singularPart_compProd', Measure.coe_add, Pi.add_apply, Measure.compProd_apply (hs.prod ht),
    Measure.compProd_apply (hs.prod ht), lintegral_measure_prod_mk_left (by simp) hs,
    lintegral_measure_prod_mk_left (by simp) hs, ν.singularPart_withDensity]
  simp only [Measure.restrict_zero, lintegral_zero_measure, zero_add]
  have : ν.withDensity (∂ν.withDensity (∂μ/∂ν)/∂ν) = ν.withDensity (∂μ/∂ν) :=
    withDensity_congr_ae (ν.rnDeriv_withDensity (μ.measurable_rnDeriv _))
  rw [this, ← setLIntegral_rnDeriv_mul (μ := ν.withDensity (∂μ/∂ν)) (ν := ν)
    (withDensity_absolutelyContinuous _ _) (Kernel.measurable_coe _ ht).aemeasurable hs]
  refine setLIntegral_congr_fun hs ?_
  filter_upwards [ν.rnDeriv_withDensity (μ.measurable_rnDeriv ν)] with x hx _
  rw [hx, Kernel.singularPart_eq_singularPart_measure]

lemma lintegral_rnDeriv_mul_singularPart (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a, (∂μ/∂ν) a * (κ a).singularPart (η a) t ∂ν
      = ((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) (.univ ×ˢ t) := by
  rw [← setLIntegral_rnDeriv_mul_singularPart _ _ _ _ .univ ht, setLIntegral_univ]

lemma setLIntegral_withDensity (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a in s, η.withDensity (κ.rnDeriv η) a t ∂μ
      = (μ ⊗ₘ η).withDensity (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (s ×ˢ t) := by
  rw [← setLIntegral_rnDeriv_mul_withDensity μ μ κ η hs ht]
  refine setLIntegral_congr_fun hs ?_
  filter_upwards [μ.rnDeriv_self] with a ha _
  rw [ha, one_mul]

lemma setLIntegral_singularPart (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a in s, (κ a).singularPart (η a) t ∂μ = (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) (s ×ˢ t) := by
  rw [singularPart_compProd_right, Measure.compProd_apply (hs.prod ht)]
  simp only [Kernel.singularPart_eq_singularPart_measure]
  rw [lintegral_measure_prod_mk_left (fun _ ↦ by simp) hs]

lemma lintegral_withDensity (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ a, η.withDensity (κ.rnDeriv η) a s ∂μ
      = (μ ⊗ₘ η).withDensity (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (.univ ×ˢ s) := by
  rw [← setLIntegral_univ, setLIntegral_withDensity _ _ _ .univ hs]

lemma lintegral_singularPart (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ a, (κ a).singularPart (η a) s ∂μ = (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) (.univ ×ˢ s) := by
  rw [← setLIntegral_univ, setLIntegral_singularPart _ _ _ .univ hs]

lemma integrable_rnDeriv_mul_withDensity (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Integrable (fun x ↦ ((∂μ/∂ν) x).toReal * (η.withDensity (κ.rnDeriv η) x .univ).toReal) ν := by
  simp_rw [← ENNReal.toReal_mul]
  refine integrable_toReal_of_lintegral_ne_top ?_ (ne_of_lt ?_)
  · refine (μ.measurable_rnDeriv _).aemeasurable.mul ?_
    exact (Kernel.measurable_coe _ .univ).aemeasurable
  rw [lintegral_rnDeriv_mul_withDensity _ _ _ _ .univ]
  exact measure_lt_top _ _

lemma integrable_rnDeriv_mul_singularPart
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Integrable (fun x ↦ ((∂μ/∂ν) x).toReal * ((κ x).singularPart (η x) .univ).toReal) ν := by
  simp_rw [← ENNReal.toReal_mul]
  refine integrable_toReal_of_lintegral_ne_top ?_ (ne_of_lt ?_)
  · simp_rw [← Kernel.singularPart_eq_singularPart_measure]
    refine (μ.measurable_rnDeriv _).aemeasurable.mul ?_
    exact (Kernel.measurable_coe _ .univ).aemeasurable
  rw [lintegral_rnDeriv_mul_singularPart _ _ _ _ .univ]
  exact measure_lt_top _ _

lemma integrable_singularPart [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    Integrable (fun x ↦ ((κ x).singularPart (η x) .univ).toReal) μ := by
  refine integrable_toReal_of_lintegral_ne_top ?_ (ne_of_lt ?_)
  · simp_rw [← Kernel.singularPart_eq_singularPart_measure]
    exact (Kernel.measurable_coe _ .univ).aemeasurable
  rw [lintegral_singularPart _ _ _ .univ]
  exact measure_lt_top _ _

lemma setIntegral_rnDeriv_mul_withDensity
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫ a in s, ((∂μ/∂ν) a).toReal *(η.withDensity (κ.rnDeriv η) a t).toReal ∂ν
      = ((ν ⊗ₘ η).withDensity (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (s ×ˢ t)).toReal := by
  rw [← setLIntegral_rnDeriv_mul_withDensity _ _ _ _ hs ht]
  simp_rw [← ENNReal.toReal_mul]
  rw [integral_toReal]
  · refine AEMeasurable.mul ?_ ?_
    · exact (μ.measurable_rnDeriv _).aemeasurable
    · exact (Kernel.measurable_coe _ ht).aemeasurable
  · refine ae_restrict_of_ae ?_
    filter_upwards [μ.rnDeriv_lt_top ν] with a ha
    exact ENNReal.mul_lt_top ha (measure_lt_top _ _)

lemma integral_rnDeriv_mul_withDensity
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {t : Set β} (ht : MeasurableSet t) :
    ∫ a, ((∂μ/∂ν) a).toReal *(η.withDensity (κ.rnDeriv η) a t).toReal ∂ν
      = ((ν ⊗ₘ η).withDensity (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (.univ ×ˢ t)).toReal := by
  rw [← setIntegral_rnDeriv_mul_withDensity μ ν κ η .univ ht, setIntegral_univ]

lemma setIntegral_rnDeriv_mul_singularPart
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫ a in s, ((∂μ/∂ν) a).toReal * ((κ a).singularPart (η a) t).toReal ∂ν
      = (((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) (s ×ˢ t)).toReal := by
  rw [← setLIntegral_rnDeriv_mul_singularPart _ _ _ _ hs ht]
  simp_rw [← ENNReal.toReal_mul]
  rw [integral_toReal]
  · simp_rw [← Kernel.singularPart_eq_singularPart_measure]
    refine AEMeasurable.mul ?_ ?_
    · exact (μ.measurable_rnDeriv _).aemeasurable
    · exact (Kernel.measurable_coe _ ht).aemeasurable
  · refine ae_restrict_of_ae ?_
    filter_upwards [μ.rnDeriv_lt_top ν] with a ha using ENNReal.mul_lt_top ha (measure_lt_top _ _)

lemma integral_rnDeriv_mul_singularPart
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {t : Set β} (ht : MeasurableSet t) :
    ∫ a, ((∂μ/∂ν) a).toReal * ((κ a).singularPart (η a) t).toReal ∂ν
      = (((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) (.univ ×ˢ t)).toReal := by
  rw [← setIntegral_rnDeriv_mul_singularPart μ ν κ η .univ ht, setIntegral_univ]

lemma setIntegral_singularPart
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫ a in s, ((κ a).singularPart (η a) t).toReal ∂μ
      = ((μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) (s ×ˢ t)).toReal := by
  rw [← setLIntegral_singularPart _ _ _ hs ht, integral_toReal]
  · simp_rw [← Kernel.singularPart_eq_singularPart_measure]
    exact (Kernel.measurable_coe _ ht).aemeasurable
  · exact ae_of_all _ (fun _ ↦ measure_lt_top _ _)

lemma integral_singularPart
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set β} (hs : MeasurableSet s) :
    ∫ a, ((κ a).singularPart (η a) s).toReal ∂μ
      = ((μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) (.univ ×ˢ s)).toReal := by
  rw [← setIntegral_univ, setIntegral_singularPart _ _ _ .univ hs]

end IntegralRnDeriv

--Maybe there is already something like this in mathlib? I couldn't find it.
--Is this name (`ProbabilityTheory.Integrable.Kernel`) ok?
lemma Integrable.Kernel [IsFiniteKernel κ] [IsFiniteMeasure μ] (s : Set β) (hs : MeasurableSet s) :
  Integrable (fun x ↦ ((κ x) s).toReal) μ := by
obtain ⟨C, ⟨hC_finite, hC_le⟩⟩ := IsFiniteKernel.exists_univ_le (κ := κ)
apply (integrable_const C.toReal).mono'
· exact κ.measurable_coe hs |>.ennreal_toReal.aestronglyMeasurable
simp_rw [Real.norm_eq_abs, abs_eq_self.mpr ENNReal.toReal_nonneg, ENNReal.toReal_le_toReal
  (measure_ne_top _ _) (lt_top_iff_ne_top.mp hC_finite)]
exact .of_forall <| fun x ↦ (κ x).mono s.subset_univ |>.trans (hC_le x)

lemma Measure.rnDeriv_measure_compProd_Kernel_withDensity [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (∂μ ⊗ₘ (η.withDensity (κ.rnDeriv η))/∂ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) := by
  let κ' := η.withDensity (κ.rnDeriv η)
  have h_ae : ∀ᵐ p ∂(ν ⊗ₘ η), κ'.rnDeriv η p.1 p.2 = κ.rnDeriv η p.1 p.2 := by
    refine Kernel.ENNReal.ae_eq_compProd_of_forall_ae_eq ν η ?_ ?_ ?_
    · exact κ'.measurable_rnDeriv _
    · exact κ.measurable_rnDeriv _
    · exact fun a ↦ η.rnDeriv_withDensity (κ.measurable_rnDeriv _) a
  filter_upwards [κ.rnDeriv_measure_compProd μ ν η,
      κ'.rnDeriv_measure_compProd μ ν η, h_ae] with p h1 h2 h3
  rw [h1, h2, h3]

end ProbabilityTheory

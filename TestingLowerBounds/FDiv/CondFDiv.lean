/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.MeasureCompProd
import TestingLowerBounds.FDiv.Basic
import Mathlib.Probability.Kernel.Disintegration.Basic

/-!

# f-Divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open Real MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : kernel α β} {f g : ℝ → ℝ}

-- todo name
lemma lintegral_measure_prod_mk_left {f : α → Set β → ℝ≥0∞} (hf : ∀ a, f a ∅ = 0)
    {s : Set α} (hs : MeasurableSet s) (t : Set β) :
    ∫⁻ a, f a (Prod.mk a ⁻¹' s ×ˢ t) ∂μ = ∫⁻ a in s, f a t ∂μ := by
  rw [← lintegral_indicator _ hs]
  congr with a
  classical
  rw [Set.indicator_apply]
  split_ifs with ha <;> simp [ha, hf]

lemma set_lintegral_rnDeriv_mul_withDensity [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a in s, (∂μ/∂ν) a * kernel.withDensity η (kernel.rnDeriv κ η) a t ∂ν
      = (ν ⊗ₘ η).withDensity (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (s ×ˢ t) := by
  have : ∀ a, kernel.withDensity η (kernel.rnDeriv κ η) a t
      = ∫⁻ y in t, kernel.rnDeriv κ η a y ∂(η a) := by
    intro a
    rw [kernel.withDensity_apply']
    exact kernel.measurable_rnDeriv _ _
  simp_rw [this]
  rw [withDensity_apply _ (hs.prod ht),
    Measure.set_lintegral_compProd (Measure.measurable_rnDeriv _ _) hs ht]
  refine set_lintegral_congr_fun hs ?_
  filter_upwards [kernel.rnDeriv_measure_compProd' μ ν κ η] with a ha _
  rw [← lintegral_const_mul _ (kernel.measurable_rnDeriv_right _ _ _)]
  refine set_lintegral_congr_fun ht ?_
  filter_upwards [ha, kernel.rnDeriv_eq_rnDeriv_measure κ η a] with b hb hb' _
  rw [hb, hb']

lemma lintegral_rnDeriv_mul_withDensity [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a, (∂μ/∂ν) a * kernel.withDensity η (kernel.rnDeriv κ η) a t ∂ν
      = (ν ⊗ₘ η).withDensity (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (Set.univ ×ˢ t) := by
  rw [← set_lintegral_rnDeriv_mul_withDensity _ _ _ _ MeasurableSet.univ ht, set_lintegral_univ]

lemma set_lintegral_rnDeriv_mul_singularPart [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a in s, (∂μ/∂ν) a * (κ a).singularPart (η a) t ∂ν
      = ((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) (s ×ˢ t) := by
  rw [singularPart_compProd', Measure.coe_add, Pi.add_apply, Measure.compProd_apply (hs.prod ht),
    Measure.compProd_apply (hs.prod ht), lintegral_measure_prod_mk_left (by simp) hs,
    lintegral_measure_prod_mk_left (by simp) hs, Measure.singularPart_withDensity ν]
  simp only [Measure.restrict_zero, lintegral_zero_measure, zero_add]
  have : Measure.withDensity ν (∂Measure.withDensity ν (∂μ/∂ν)/∂ν)
      = Measure.withDensity ν (∂μ/∂ν) :=
    withDensity_congr_ae (Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _))
  rw [this, ← set_lintegral_rnDeriv_mul (μ := ν.withDensity (∂μ/∂ν)) (ν := ν)
    (withDensity_absolutelyContinuous _ _) (kernel.measurable_coe _ ht).aemeasurable hs]
  refine set_lintegral_congr_fun hs ?_
  filter_upwards [Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv μ ν)] with x hx _
  rw [hx, kernel.singularPart_eq_singularPart_measure]

lemma lintegral_rnDeriv_mul_singularPart [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a, (∂μ/∂ν) a * (κ a).singularPart (η a) t ∂ν
      = ((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) (Set.univ ×ˢ t) := by
  rw [← set_lintegral_rnDeriv_mul_singularPart _ _ _ _ MeasurableSet.univ ht, set_lintegral_univ]

lemma set_lintegral_withDensity [MeasurableSpace.CountablyGenerated β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a in s, kernel.withDensity η (kernel.rnDeriv κ η) a t ∂μ
      = (μ ⊗ₘ η).withDensity (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (s ×ˢ t) := by
  rw [← set_lintegral_rnDeriv_mul_withDensity μ μ κ η hs ht]
  refine set_lintegral_congr_fun hs ?_
  filter_upwards [μ.rnDeriv_self] with a ha _
  rw [ha, one_mul]

lemma set_lintegral_singularPart [MeasurableSpace.CountablyGenerated β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a in s, (κ a).singularPart (η a) t ∂μ = (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) (s ×ˢ t) := by
  rw [singularPart_compProd_right, Measure.compProd_apply (hs.prod ht)]
  simp only [kernel.singularPart_eq_singularPart_measure]
  rw [lintegral_measure_prod_mk_left (fun _ ↦ by simp) hs]

lemma lintegral_withDensity [MeasurableSpace.CountablyGenerated β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ a, kernel.withDensity η (kernel.rnDeriv κ η) a s ∂μ
      = (μ ⊗ₘ η).withDensity (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (Set.univ ×ˢ s) := by
  rw [← set_lintegral_univ, set_lintegral_withDensity _ _ _ MeasurableSet.univ hs]

lemma lintegral_singularPart [MeasurableSpace.CountablyGenerated β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ a, (κ a).singularPart (η a) s ∂μ = (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) (Set.univ ×ˢ s) := by
  rw [← set_lintegral_univ, set_lintegral_singularPart _ _ _ MeasurableSet.univ hs]

lemma integrable_rnDeriv_mul_withDensity [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Integrable (fun x ↦
      ((∂μ/∂ν) x).toReal * (kernel.withDensity η (kernel.rnDeriv κ η) x Set.univ).toReal) ν := by
  simp_rw [← ENNReal.toReal_mul]
  refine integrable_toReal_of_lintegral_ne_top ?_ (ne_of_lt ?_)
  · refine AEMeasurable.mul ?_ ?_
    · exact (Measure.measurable_rnDeriv _ _).aemeasurable
    · exact (kernel.measurable_coe _ MeasurableSet.univ).aemeasurable
  rw [lintegral_rnDeriv_mul_withDensity _ _ _ _ MeasurableSet.univ]
  exact measure_lt_top _ _

lemma integrable_rnDeriv_mul_singularPart [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Integrable (fun x ↦ ((∂μ/∂ν) x).toReal * ((κ x).singularPart (η x) Set.univ).toReal) ν := by
  simp_rw [← ENNReal.toReal_mul]
  refine integrable_toReal_of_lintegral_ne_top ?_ (ne_of_lt ?_)
  · simp_rw [← kernel.singularPart_eq_singularPart_measure]
    refine AEMeasurable.mul ?_ ?_
    · exact (Measure.measurable_rnDeriv _ _).aemeasurable
    · exact (kernel.measurable_coe _ MeasurableSet.univ).aemeasurable
  rw [lintegral_rnDeriv_mul_singularPart _ _ _ _ MeasurableSet.univ]
  exact measure_lt_top _ _

lemma integrable_singularPart [MeasurableSpace.CountablyGenerated β] [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    Integrable (fun x ↦ ((κ x).singularPart (η x) Set.univ).toReal) μ := by
  refine integrable_toReal_of_lintegral_ne_top ?_ (ne_of_lt ?_)
  · simp_rw [← kernel.singularPart_eq_singularPart_measure]
    exact (kernel.measurable_coe _ MeasurableSet.univ).aemeasurable
  rw [lintegral_singularPart _ _ _ MeasurableSet.univ]
  exact measure_lt_top _ _

lemma set_integral_rnDeriv_mul_withDensity [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫ a in s, ((∂μ/∂ν) a).toReal *(kernel.withDensity η (kernel.rnDeriv κ η) a t).toReal ∂ν
      = ((ν ⊗ₘ η).withDensity (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (s ×ˢ t)).toReal := by
  rw [← set_lintegral_rnDeriv_mul_withDensity _ _ _ _ hs ht]
  simp_rw [← ENNReal.toReal_mul]
  rw [integral_toReal]
  · refine AEMeasurable.mul ?_ ?_
    · exact (Measure.measurable_rnDeriv _ _).aemeasurable
    · exact (kernel.measurable_coe _ ht).aemeasurable
  · refine ae_restrict_of_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top μ ν] with a ha
    exact ENNReal.mul_lt_top ha.ne (measure_ne_top _ _)

lemma integral_rnDeriv_mul_withDensity [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {t : Set β} (ht : MeasurableSet t) :
    ∫ a, ((∂μ/∂ν) a).toReal *(kernel.withDensity η (kernel.rnDeriv κ η) a t).toReal ∂ν
      = ((ν ⊗ₘ η).withDensity (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (Set.univ ×ˢ t)).toReal := by
  rw [← set_integral_rnDeriv_mul_withDensity μ ν κ η MeasurableSet.univ ht, integral_univ]

lemma set_integral_rnDeriv_mul_singularPart [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫ a in s, ((∂μ/∂ν) a).toReal * ((κ a).singularPart (η a) t).toReal ∂ν
      = (((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) (s ×ˢ t)).toReal := by
  rw [← set_lintegral_rnDeriv_mul_singularPart _ _ _ _ hs ht]
  simp_rw [← ENNReal.toReal_mul]
  rw [integral_toReal]
  · simp_rw [← kernel.singularPart_eq_singularPart_measure]
    refine AEMeasurable.mul ?_ ?_
    · exact (Measure.measurable_rnDeriv _ _).aemeasurable
    · exact (kernel.measurable_coe _ ht).aemeasurable
  · refine ae_restrict_of_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top μ ν] with a ha
    exact ENNReal.mul_lt_top ha.ne (measure_ne_top _ _)

lemma integral_rnDeriv_mul_singularPart [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {t : Set β} (ht : MeasurableSet t) :
    ∫ a, ((∂μ/∂ν) a).toReal * ((κ a).singularPart (η a) t).toReal ∂ν
      = (((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) (Set.univ ×ˢ t)).toReal := by
  rw [← set_integral_rnDeriv_mul_singularPart μ ν κ η MeasurableSet.univ ht, integral_univ]

lemma set_integral_singularPart [MeasurableSpace.CountablyGenerated β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫ a in s, ((κ a).singularPart (η a) t).toReal ∂μ
      = ((μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) (s ×ˢ t)).toReal := by
  rw [← set_lintegral_singularPart _ _ _ hs ht, integral_toReal]
  · simp_rw [← kernel.singularPart_eq_singularPart_measure]
    exact (kernel.measurable_coe _ ht).aemeasurable
  · exact ae_of_all _ (fun _ ↦ measure_lt_top _ _)

lemma integral_singularPart [MeasurableSpace.CountablyGenerated β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set β} (hs : MeasurableSet s) :
    ∫ a, ((κ a).singularPart (η a) s).toReal ∂μ
      = ((μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) (Set.univ ×ˢ s)).toReal := by
  rw [← integral_univ, set_integral_singularPart _ _ _ MeasurableSet.univ hs]

section Conditional

-- TODO: explain that we should not use these hypotheses in lemmas, but equivalent ones.
open Classical in
/-- Conditional f-divergence. -/
noncomputable
def condFDiv (f : ℝ → ℝ) (κ η : kernel α β) (μ : Measure α) : EReal :=
  if (∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    ∧ (Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ)
  then ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal)
  else ⊤

lemma condFDiv_of_not_ae_finite (hf : ¬ ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤) :
    condFDiv f κ η μ = ⊤ := by
  rw [condFDiv, if_neg]
  push_neg
  exact fun h ↦ absurd h hf

lemma condFDiv_of_not_integrable
    (hf : ¬ Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) :
    condFDiv f κ η μ = ⊤ := by
  rw [condFDiv, if_neg]
  push_neg
  exact fun _ ↦ hf

/- Use condFDiv_eq instead: its assumptions are in normal form. -/
lemma condFDiv_eq' (hf_ae : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    (hf : Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) :
    condFDiv f κ η μ = ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal) :=
  if_pos ⟨hf_ae, hf⟩

lemma condFDiv_nonneg [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf_one : f 1 = 0) : 0 ≤ condFDiv f κ η μ := by
  by_cases h_ae : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤
  swap; · rw[condFDiv_of_not_ae_finite h_ae]; exact le_top
  by_cases h_int : Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ
  swap; · rw[condFDiv_of_not_integrable h_int]; exact le_top
  rw [condFDiv_eq' h_ae h_int]
  simp only [EReal.coe_nonneg]
  apply integral_nonneg _
  intro x
  have h := @fDiv_nonneg _ _ (κ x) (η x) f _ _ hf_cvx hf_cont hf_one
  simp [EReal.toReal_nonneg, h]

variable [MeasurableSpace.CountablyGenerated β]

section Integrable

/-! We show that the integrability of the functions used in `fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η)`
and in `condFDiv f κ η μ` are equivalent. -/

lemma fDiv_compProd_ne_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ⊤ ↔
      (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a)) ν
        ∧ (derivAtTop f = ⊤ → μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [fDiv_ne_top_iff, integrable_f_rnDeriv_compProd_iff hf h_cvx,
    kernel.Measure.absolutelyContinuous_compProd_iff, and_assoc]

lemma fDiv_compProd_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) = ⊤ ↔
      (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a)) →
        Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂η a) ν →
        derivAtTop f = ⊤ ∧ (μ ≪ ν → ¬∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_ne_top_iff hf h_cvx]
  push_neg
  rfl

lemma fDiv_compProd_right_ne_top_iff [IsFiniteMeasure μ]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ⊤ ↔
      (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a)) μ
        ∧ (derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [fDiv_compProd_ne_top_iff hf h_cvx]
  have h_self := μ.rnDeriv_self
  refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun h ↦ ⟨?_, ?_, ?_⟩⟩
  · filter_upwards [h_self, h.1] with a ha1 ha2
    simp_rw [ha1, one_mul] at ha2
    exact ha2
  · refine (integrable_congr ?_).mp h.2.1
    filter_upwards [h_self] with a ha1
    simp_rw [ha1, one_mul]
  · simp only [Measure.AbsolutelyContinuous.rfl, true_and] at h
    exact h.2.2
  · filter_upwards [h_self, h.1] with a ha1 ha2
    simp_rw [ha1, one_mul]
    exact ha2
  · refine (integrable_congr ?_).mp h.2.1
    filter_upwards [h_self] with a ha1
    simp_rw [ha1, one_mul]
  · simp only [Measure.AbsolutelyContinuous.rfl, true_and]
    exact h.2.2

lemma fDiv_compProd_right_eq_top_iff [IsFiniteMeasure μ]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = ⊤ ↔
      (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a)) →
        Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ →
        derivAtTop f = ⊤ ∧ ¬∀ᵐ a ∂μ, κ a ≪ η a := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_right_ne_top_iff hf h_cvx]
  push_neg
  rfl

lemma fDiv_compProd_left_ne_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) ≠ ⊤ ↔
      Integrable (fun a ↦ f ((∂μ/∂ν) a).toReal) ν ∧ (derivAtTop f = ⊤ → μ ≪ ν) := by
  rw [fDiv_compProd_ne_top_iff hf h_cvx]
  have h_one : ∀ a, ∂(κ a)/∂(κ a) =ᵐ[κ a] 1 := fun a ↦ Measure.rnDeriv_self (κ a)
  simp only [ENNReal.toReal_mul, Measure.AbsolutelyContinuous.rfl, eventually_true, and_true]
  have : ∀ a, ∫ b, f (((∂μ/∂ν) a).toReal * ((∂κ a/∂κ a) b).toReal) ∂κ a
        = ∫ _, f (((∂μ/∂ν) a).toReal) ∂κ a := by
      refine fun a ↦ integral_congr_ae ?_
      filter_upwards [h_one a] with b hb
      simp [hb]
  refine ⟨fun ⟨_, h2, h3⟩ ↦ ⟨?_, h3⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, ?_, h2⟩⟩
  · refine (integrable_congr ?_).mpr h2
    refine ae_of_all _ (fun a ↦ ?_)
    simp only
    simp [this]
  · refine ae_of_all _ (fun a ↦ ?_)
    have : (fun x ↦ f (((∂μ/∂ν) a).toReal * ((∂κ a/∂κ a) x).toReal))
        =ᵐ[κ a] (fun _ ↦ f ((∂μ/∂ν) a).toReal) := by
      filter_upwards [h_one a] with b hb
      simp [hb]
    rw [integrable_congr this]
    simp
  · simp only [this, integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
    exact h1

lemma fDiv_compProd_left_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = ⊤ ↔
      Integrable (fun a ↦ f ((∂μ/∂ν) a).toReal) ν → (derivAtTop f = ⊤ ∧ ¬ μ ≪ ν) := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_left_ne_top_iff hf h_cvx]
  push_neg
  rfl

lemma integrable_fDiv_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_fin : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤) :
    Integrable (fun x ↦ EReal.toReal (fDiv f (κ x) (η x))) μ
      ↔ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ := by
  by_cases h_top : derivAtTop f = ⊤
  · classical
    simp_rw [fDiv_of_derivAtTop_eq_top h_top]
    simp only [fDiv_ne_top_iff, h_top, forall_true_left] at h_fin
    refine integrable_congr ?_
    filter_upwards [h_fin] with a ha
    rw [if_pos ha, EReal.toReal_coe]
  · have h_fin' := h_fin
    simp_rw [fDiv_ne_top_iff_of_derivAtTop_ne_top h_top] at h_fin
    have : (fun x ↦ (fDiv f (κ x) (η x)).toReal)
        =ᵐ[μ] (fun x ↦ ∫ y, f ((∂κ x/∂η x) y).toReal ∂(η x)
          + (derivAtTop f).toReal * ((κ x).singularPart (η x) Set.univ).toReal) := by
      filter_upwards [h_fin'] with x hx1
      rw [fDiv_of_ne_top hx1, EReal.toReal_add]
      · simp only [EReal.toReal_coe, add_right_inj]
        rw [EReal.toReal_mul]
        simp
      · simp
      · simp
      · simp [h_top, EReal.mul_eq_top, derivAtTop_ne_bot, measure_ne_top]
      · simp [EReal.mul_eq_bot, derivAtTop_ne_bot, h_top, measure_ne_top]
    rw [integrable_congr this]
    have h_int : Integrable (fun x ↦ (derivAtTop f).toReal
        * ((κ x).singularPart (η x) Set.univ).toReal) μ := by
      refine Integrable.const_mul ?_ (derivAtTop f).toReal
      exact integrable_singularPart
    refine ⟨fun h ↦ ?_, fun h ↦ h.add h_int⟩
    have : (fun x ↦ ∫ y, f ((∂κ x/∂η x) y).toReal ∂η x)
        = (fun x ↦ (∫ y, f ((∂κ x/∂η x) y).toReal ∂η x +
          (derivAtTop f).toReal * ((κ x).singularPart (η x) Set.univ).toReal)
          - (derivAtTop f).toReal * ((κ x).singularPart (η x) Set.univ).toReal) := by
      ext; simp
    rw [this]
    exact h.sub h_int

lemma condFDiv_ne_top_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
  condFDiv f κ η μ ≠ ⊤ ↔
    (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
      ∧ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a)) μ
      ∧ (derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [condFDiv]
  split_ifs with h
  · have h' := h
    simp_rw [fDiv_ne_top_iff] at h
    simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, true_iff]
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [h.1] with a ha
      exact ha.1
    · have h_int := h.2
      rwa [integrable_fDiv_iff h'.1] at h_int
    · intro h_top
      filter_upwards [h.1] with a ha
      exact ha.2 h_top
  · simp only [ne_eq, not_true_eq_false, false_iff, not_and, not_forall, not_eventually,
      exists_prop]
    push_neg at h
    intro hf_int h_int
    simp_rw [fDiv_ne_top_iff] at h
    by_contra h_contra
    simp only [not_and, not_frequently, not_not] at h_contra
    rw [eventually_and] at h
    simp only [hf_int, eventually_all, true_and] at h
    specialize h h_contra
    have h_top : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤ := by
      simp only [ne_eq, fDiv_ne_top_iff, eventually_and, eventually_all]
      exact ⟨hf_int, h_contra⟩
    rw [integrable_fDiv_iff h_top] at h
    exact h h_int

lemma condFDiv_eq [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hf_ae : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (hf : Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ)
    (h_deriv : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    condFDiv f κ η μ = ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal) := by
  have h_ne : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤ := by
    simp only [ne_eq, fDiv_ne_top_iff, eventually_and, hf_ae, eventually_all, true_and]
    exact h_deriv
  refine condFDiv_eq' h_ne ?_
  rwa [integrable_fDiv_iff h_ne]

lemma condFDiv_ne_top_iff_fDiv_compProd_ne_top [IsFiniteMeasure μ]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    condFDiv f κ η μ ≠ ⊤ ↔ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ⊤ := by
  rw [condFDiv_ne_top_iff, fDiv_compProd_right_ne_top_iff hf h_cvx]

lemma condFDiv_eq_top_iff_fDiv_compProd_eq_top [IsFiniteMeasure μ]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    condFDiv f κ η μ = ⊤ ↔ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = ⊤ := by
  rw [← not_iff_not]
  exact condFDiv_ne_top_iff_fDiv_compProd_ne_top hf h_cvx

lemma condFDiv_eq_add [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hf_ae : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (hf : Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ)
    (h_deriv : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    condFDiv f κ η μ = (μ[fun a ↦ ∫ y, f ((∂κ a/∂η a) y).toReal ∂η a] : ℝ)
      + (derivAtTop f).toReal * (μ[fun a ↦ ((κ a).singularPart (η a) Set.univ).toReal] : ℝ) := by
  rw [condFDiv_eq hf_ae hf h_deriv]
  have : (fun x ↦ (fDiv f (κ x) (η x)).toReal)
      =ᵐ[μ] fun x ↦ ∫ y, f ((∂(κ x)/∂(η x)) y).toReal ∂(η x)
        + (derivAtTop f * (κ x).singularPart (η x) Set.univ).toReal := by
    have h_deriv' : ∀ᵐ a ∂μ, derivAtTop f = ⊤ → κ a ≪ η a := by
      simpa only [eventually_all] using h_deriv
    filter_upwards [hf_ae, h_deriv'] with x hx hx_deriv
    exact toReal_fDiv_of_integrable hx hx_deriv
  rw [integral_congr_ae this, integral_add]
  rotate_left
  · exact hf
  · simp_rw [EReal.toReal_mul]
    convert (integrable_singularPart (κ := κ) (η := η) (μ := μ)).const_mul (derivAtTop f).toReal
    rw [← EReal.coe_ennreal_toReal, EReal.toReal_coe]
    exact measure_ne_top _ _
  simp only [EReal.coe_add, EReal.toReal_mul]
  rw [integral_mul_left]
  simp only [_root_.EReal.toReal_coe_ennreal, EReal.coe_mul]

lemma condFDiv_of_derivAtTop_eq_top [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (hf_ae : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (hf : Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ)
    (h_top : derivAtTop f = ⊤) (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a) :
    condFDiv f κ η μ = (μ[fun a ↦ ∫ y, f ((∂κ a/∂η a) y).toReal ∂η a] : ℝ) := by
  rw [condFDiv_eq_add hf_ae hf]
  · simp [h_top]
  · exact fun _ ↦ h_ac

end Integrable

lemma fDiv_compProd_left (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = condFDiv f κ η μ := by
  by_cases hf_top : condFDiv f κ η μ = ⊤
  · rwa [hf_top, ← condFDiv_eq_top_iff_fDiv_compProd_eq_top hf h_cvx]
  have hf_top' := hf_top
  rw [← ne_eq, condFDiv_ne_top_iff] at hf_top'
  rcases hf_top' with ⟨h1, h2, h3⟩
  have h_int : Integrable (fun x ↦ f ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η) := by
    rw [integrable_f_rnDeriv_compProd_right_iff hf h_cvx]
    exact ⟨h1, h2⟩
  rw [fDiv_of_integrable h_int, condFDiv_eq_add h1 h2 h3, Measure.integral_compProd h_int,
    integral_congr_ae (integral_f_compProd_right_congr _ _ _)]
  by_cases h_deriv : derivAtTop f = ⊤
  · simp only [h_deriv, EReal.toReal_top, EReal.coe_zero, zero_mul]
    suffices (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) = 0 by
      simp [this]
    rw [Measure.singularPart_eq_zero, kernel.Measure.absolutelyContinuous_compProd_right_iff]
    exact h3 h_deriv
  · congr 1
    rw [EReal.coe_toReal h_deriv derivAtTop_ne_bot, integral_singularPart _ _ _ MeasurableSet.univ,
      EReal.coe_ennreal_toReal, Set.univ_prod_univ]
    exact measure_ne_top _ _

end Conditional

lemma fDiv_compProd_right [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : kernel α β) [IsMarkovKernel κ] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = fDiv f μ ν := by
  by_cases h_top : fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = ⊤
  · symm
    rw [h_top, fDiv_eq_top_iff]
    have h_top' := (fDiv_compProd_left_eq_top_iff hf h_cvx).mp h_top
    by_cases h : Integrable (fun a ↦ f ((∂μ/∂ν) a).toReal) ν
    · exact Or.inr (h_top' h)
    · exact Or.inl h
  · have h_top' := (fDiv_compProd_left_ne_top_iff hf h_cvx).mp h_top
    have h_top'' : fDiv f μ ν ≠ ⊤ := by rwa [fDiv_ne_top_iff]
    rw [fDiv_of_ne_top h_top, fDiv_of_ne_top h_top'']
    have h := integral_f_compProd_left_congr μ ν κ (f := f)
    simp only [measure_univ, ENNReal.one_toReal, one_mul] at h
    rw [integral_congr_ae h.symm, Measure.integral_compProd]
    · congr
      rw [singularPart_compProd_left, Measure.compProd_apply MeasurableSet.univ]
      simp
    · rw [← ne_eq, fDiv_ne_top_iff] at h_top
      exact h_top.1

lemma f_rnDeriv_ae_le_integral [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    (fun a ↦ f ((∂μ/∂ν) a * κ a Set.univ).toReal)
      ≤ᵐ[ν] fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a) := by
  have h_compProd := kernel.rnDeriv_measure_compProd' μ ν κ η
  have h_lt_top := Measure.ae_ae_of_ae_compProd <| Measure.rnDeriv_lt_top (μ ⊗ₘ κ) (ν ⊗ₘ η)
  have := Measure.integrable_toReal_rnDeriv (μ := μ ⊗ₘ κ) (ν := ν ⊗ₘ η)
  rw [Measure.integrable_compProd_iff] at this
  swap
  · refine (Measurable.stronglyMeasurable ?_).aestronglyMeasurable
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hκη' : ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → κ a ≪ η a := Measure.ae_rnDeriv_ne_zero_imp_of_ae hκη
  filter_upwards [hκη', h_compProd, h_lt_top, h_int.compProd_mk_left_ae', this.1]
    with a h_ac h_eq h_lt_top h_int' h_rnDeriv_int
  calc f ((∂μ/∂ν) a * κ a Set.univ).toReal
    = f ((∂μ/∂ν) a * ∫⁻ b, (∂κ a/∂η a) b ∂η a).toReal := by
        by_cases h0 : (∂μ/∂ν) a = 0
        · simp [h0]
        · rw [Measure.lintegral_rnDeriv (h_ac h0)]
  _ = f (∫⁻ b,(∂μ/∂ν) a * (∂κ a/∂η a) b ∂η a).toReal := by
        rw [lintegral_const_mul _ (Measure.measurable_rnDeriv _ _)]
  _ = f (∫⁻ b, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b) ∂η a).toReal := by rw [lintegral_congr_ae h_eq]
  _ = f (∫ b, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a) := by
        rw [integral_toReal _ h_lt_top]
        exact ((Measure.measurable_rnDeriv _ _).comp measurable_prod_mk_left).aemeasurable
  _ ≤ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a := by
        rw [← average_eq_integral, ← average_eq_integral]
        exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp) h_rnDeriv_int h_int'

lemma integrable_f_rnDeriv_mul_kernel [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun a ↦ f ((∂μ/∂ν) a * κ a Set.univ).toReal) ν := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun a ↦ f ((∂μ/∂ν) a * κ a Set.univ).toReal)
    (g₁ := fun x ↦ c * ((∂μ/∂ν) x * κ x Set.univ).toReal + c')
    (g₂ := fun x ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (x, b)).toReal ∂(η x))
    ?_ ?_ ?_ ?_ ?_
  · exact (hf.comp_measurable ((Measure.measurable_rnDeriv _ _).mul
      (kernel.measurable_coe _ MeasurableSet.univ)).ennreal_toReal).aestronglyMeasurable
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_ae_le_integral μ ν κ η hf_cvx hf_cont h_int hκη
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    simp_rw [ENNReal.toReal_mul]
    have h := integrable_rnDeriv_mul_withDensity μ ν κ η
    have h_ae : ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → kernel.withDensity η (kernel.rnDeriv κ η) a = κ a := by
      refine Measure.ae_rnDeriv_ne_zero_imp_of_ae ?_
      filter_upwards [hκη] with x hx
      rw [kernel.withDensity_rnDeriv_eq hx]
    refine (integrable_congr ?_).mp h
    filter_upwards [h_ae] with x hx
    by_cases h0 : (∂μ/∂ν) x = 0
    · simp [h0]
    · rw [hx h0]
  · exact h_int.integral_compProd'

lemma Measure.rnDeriv_measure_compProd_kernel_withDensity [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (∂μ ⊗ₘ (kernel.withDensity η (kernel.rnDeriv κ η))/∂ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) := by
  let κ' := kernel.withDensity η (kernel.rnDeriv κ η)
  have h_ae : ∀ᵐ p ∂(ν ⊗ₘ η), kernel.rnDeriv κ' η p.1 p.2 = kernel.rnDeriv κ η p.1 p.2 := by
    refine kernel.ENNReal.ae_eq_compProd_of_forall_ae_eq ν η ?_ ?_ ?_
    · exact kernel.measurable_rnDeriv _ _
    · exact kernel.measurable_rnDeriv _ _
    · refine fun a ↦ kernel.rnDeriv_withDensity η ?_ a
      exact kernel.measurable_rnDeriv _ _
  filter_upwards [kernel.rnDeriv_measure_compProd μ ν κ η,
      kernel.rnDeriv_measure_compProd μ ν κ' η, h_ae] with p h1 h2 h3
  rw [h1, h2, h3]

lemma integrable_f_rnDeriv_mul_withDensity [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η)) :
    Integrable (fun a ↦
      f ((∂μ/∂ν) a * kernel.withDensity η (kernel.rnDeriv κ η) a Set.univ).toReal) ν := by
  refine integrable_f_rnDeriv_mul_kernel μ ν _ η hf hf_cvx hf_cont ?_ ?_
  · refine (integrable_congr ?_).mp h_int
    filter_upwards [Measure.rnDeriv_measure_compProd_kernel_withDensity μ ν κ η] with x hx
    rw [hx]
  · exact ae_of_all _ (fun _ ↦ kernel.withDensity_absolutelyContinuous _ _)

lemma integral_f_rnDeriv_mul_le_integral [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫ x, f ((∂μ/∂ν) x * κ x Set.univ).toReal ∂ν
      ≤ ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η) := by
  rw [Measure.integral_compProd h_int]
  refine integral_mono_ae ?_ ?_ ?_
  · exact integrable_f_rnDeriv_mul_kernel μ ν κ η hf hf_cvx hf_cont h_int hκη
  · rw [integrable_f_rnDeriv_compProd_iff hf hf_cvx] at h_int
    rw [integrable_congr (integral_f_compProd_congr _ _ _ _)]
    exact h_int.2
  · exact f_rnDeriv_ae_le_integral μ ν κ η hf_cvx hf_cont h_int hκη

lemma integral_f_rnDeriv_mul_withDensity_le_integral [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η)) :
    ∫ x, f ((∂μ/∂ν) x * kernel.withDensity η (kernel.rnDeriv κ η) x Set.univ).toReal ∂ν
      ≤ ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η) := by
  calc ∫ x, f ((∂μ/∂ν) x * kernel.withDensity η (kernel.rnDeriv κ η) x Set.univ).toReal ∂ν
    ≤ ∫ x, f ((∂μ ⊗ₘ (kernel.withDensity η (kernel.rnDeriv κ η))/∂ν ⊗ₘ η) x).toReal
      ∂(ν ⊗ₘ η) := by
        refine integral_f_rnDeriv_mul_le_integral μ ν (kernel.withDensity η (kernel.rnDeriv κ η))
          η hf hf_cvx hf_cont ?_ ?_
        · refine (integrable_congr ?_).mpr h_int
          filter_upwards [Measure.rnDeriv_measure_compProd_kernel_withDensity μ ν κ η] with x hx
          rw [hx]
        · exact ae_of_all _ (fun _ ↦ kernel.withDensity_absolutelyContinuous _ _)
  _ = ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η) := by
        refine integral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_measure_compProd_kernel_withDensity μ ν κ η] with x hx
        rw [hx]

lemma f_rnDeriv_le_add [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsFiniteKernel η]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (h_deriv : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∀ᵐ a ∂ ν, f ((∂μ/∂ν) a).toReal
      ≤ f ((∂μ/∂ν) a * kernel.withDensity η (kernel.rnDeriv κ η) a Set.univ).toReal
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal
          * (kernel.singularPart κ η a Set.univ).toReal := by
  by_cases h_deriv_top : derivAtTop f = ⊤
  · simp only [ENNReal.toReal_mul, h_deriv_top, EReal.toReal_top, zero_mul, add_zero]
    have h_ae : ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → kernel.withDensity η (kernel.rnDeriv κ η) a = κ a := by
      refine Measure.ae_rnDeriv_ne_zero_imp_of_ae ?_
      filter_upwards [h_deriv h_deriv_top] with a ha_ac
      rw [kernel.withDensity_rnDeriv_eq ha_ac]
    filter_upwards [h_ae] with a ha
    by_cases h0 : (∂μ/∂ν) a = 0
    · simp [h0]
    · rw [ha h0]
      simp
  refine ae_of_all _ (fun a ↦ ?_)
  simp only [ENNReal.toReal_mul]
  let κ' := kernel.withDensity η (kernel.rnDeriv κ η)
  calc f ((∂μ/∂ν) a).toReal
  _ ≤ f (((∂μ/∂ν) a).toReal * (κ' a Set.univ).toReal)
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal * (1 - (κ' a Set.univ).toReal) := by
      refine le_add_derivAtTop' hf_cvx h_deriv_top ENNReal.toReal_nonneg ENNReal.toReal_nonneg ?_
      calc (κ' a Set.univ).toReal
      _ ≤ (κ a Set.univ).toReal := by
          gcongr
          · exact measure_ne_top _ _
          · exact kernel.withDensity_rnDeriv_le κ η a Set.univ
      _ = 1 := by simp
  _ = f (((∂μ/∂ν) a).toReal * (κ' a Set.univ).toReal)
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal
          * (kernel.singularPart κ η a Set.univ).toReal := by
      congr
      norm_cast
      unfold_let κ'
      rw [sub_eq_iff_eq_add, ← ENNReal.one_toReal, ← measure_univ (μ := κ a)]
      conv_lhs => rw [← kernel.rnDeriv_add_singularPart κ η, add_comm]
      simp only [kernel.coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure, OuterMeasure.coe_add]
      rw [ENNReal.toReal_add]
      · exact measure_ne_top _ _
      · exact measure_ne_top _ _

lemma integrable_f_rnDeriv_of_integrable_compProd' [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (h_deriv : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun a ↦ f ((∂μ/∂ν) a).toReal)
    (g₁ := fun a ↦ c * ((∂μ/∂ν) a).toReal + c')
    (g₂ := fun a ↦ f ((∂μ/∂ν) a * kernel.withDensity η (kernel.rnDeriv κ η) a Set.univ).toReal
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal
          * (kernel.singularPart κ η a Set.univ).toReal)
    ?_ ?_ ?_ ?_ ?_
  · exact (hf.comp_measurable (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_le_add μ ν κ η hf_cvx h_deriv
  · exact (Measure.integrable_toReal_rnDeriv.const_mul _).add (integrable_const _)
  · refine Integrable.add ?_ ?_
    · exact integrable_f_rnDeriv_mul_withDensity μ ν κ η hf hf_cvx hf_cont hf_int
    · simp_rw [mul_assoc]
      refine Integrable.const_mul ?_ _
      simp_rw [kernel.singularPart_eq_singularPart_measure]
      exact integrable_rnDeriv_mul_singularPart _ _ _ _

lemma fDiv_ne_top_of_fDiv_compProd_ne_top [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_ne_top : fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ⊤) :
    fDiv f μ ν ≠ ⊤ := by
  rw [fDiv_ne_top_iff]
  have h_ne_top' := (fDiv_compProd_ne_top_iff hf hf_cvx).mp h_ne_top
  obtain ⟨h1, h2, h3⟩ := h_ne_top'
  refine ⟨?_, fun h_top ↦ (h3 h_top).1⟩
  rw [fDiv_ne_top_iff] at h_ne_top
  exact integrable_f_rnDeriv_of_integrable_compProd' μ ν κ η hf hf_cvx hf_cont h_ne_top.1
    (fun h ↦ (h3 h).2)

lemma integral_f_rnDeriv_le_integral_add [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (h_deriv : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫ x, f ((∂μ/∂ν) x).toReal ∂ν
      ≤ ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η)
      + (derivAtTop f).toReal
        * ∫ a, ((∂μ/∂ν) a).toReal * (kernel.singularPart κ η a Set.univ).toReal ∂ν := by
  suffices ∫ x, f ((∂μ/∂ν) x).toReal ∂ν
      ≤ ∫ x, f ((∂μ/∂ν) x * kernel.withDensity η (kernel.rnDeriv κ η) x Set.univ).toReal ∂ν
      + (derivAtTop f).toReal
        * ∫ a, ((∂μ/∂ν) a).toReal * (kernel.singularPart κ η a Set.univ).toReal ∂ν by
    refine this.trans ?_
    gcongr
    exact integral_f_rnDeriv_mul_withDensity_le_integral μ ν κ η hf hf_cvx hf_cont h_int
  let κ' := kernel.withDensity η (kernel.rnDeriv κ η)
  have h : ∀ᵐ a ∂ν, f ((∂μ/∂ν) a).toReal
      ≤ f ((∂μ/∂ν) a * κ' a Set.univ).toReal
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal
          * (kernel.singularPart κ η a Set.univ).toReal :=
    f_rnDeriv_le_add _ _ _ _ hf_cvx h_deriv
  have h_int_mul : Integrable (fun a ↦ f ((∂μ/∂ν) a * κ' a Set.univ).toReal) ν :=
    integrable_f_rnDeriv_mul_withDensity μ ν κ η hf hf_cvx hf_cont h_int
  have h_int_right : Integrable (fun a ↦ (derivAtTop f).toReal
      * ((∂μ/∂ν) a).toReal * (kernel.singularPart κ η a Set.univ).toReal) ν := by
    simp_rw [mul_assoc]
    refine Integrable.const_mul ?_ _
    simp_rw [kernel.singularPart_eq_singularPart_measure]
    exact integrable_rnDeriv_mul_singularPart _ _ _ _
  refine (integral_mono_ae ?_ ?_ h).trans_eq ?_
  · exact integrable_f_rnDeriv_of_integrable_compProd' μ ν κ η hf hf_cvx hf_cont h_int h_deriv
  · exact h_int_mul.add h_int_right
  rw [integral_add h_int_mul h_int_right]
  unfold_let κ'
  simp_rw [mul_assoc]
  rw [integral_mul_left]

lemma le_fDiv_compProd [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) :
    fDiv f μ ν ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  by_cases h_top : fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) = ⊤
  · simp [h_top]
  rw [fDiv_of_ne_top (fDiv_ne_top_of_fDiv_compProd_ne_top μ ν κ η hf hf_cvx hf_cont h_top),
    fDiv_of_ne_top h_top]
  obtain h_int := (fDiv_ne_top_iff.mp h_top).1
  rw [← ne_eq, fDiv_compProd_ne_top_iff hf hf_cvx] at h_top
  obtain ⟨_, _, h3⟩ := h_top
  calc ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * Measure.singularPart μ ν Set.univ
    ≤ ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η)
      + (derivAtTop f).toReal
        * ∫ a, ((∂μ/∂ν) a).toReal * (kernel.singularPart κ η a Set.univ).toReal ∂ν
      + derivAtTop f * Measure.singularPart μ ν Set.univ := by
        gcongr
        norm_cast
        exact integral_f_rnDeriv_le_integral_add μ ν κ η hf hf_cvx hf_cont h_int (fun h ↦ (h3 h).2)
  _ = ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η)
      + (derivAtTop f).toReal
        * (((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) Set.univ).toReal
      + derivAtTop f * Measure.singularPart μ ν Set.univ := by
        simp_rw [kernel.singularPart_eq_singularPart_measure]
        rw [integral_rnDeriv_mul_singularPart _ _ _ _ MeasurableSet.univ, Set.univ_prod_univ]
  _ = ∫ p, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal ∂ν ⊗ₘ η
      + derivAtTop f * (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η) Set.univ := by
        rw [add_assoc]
        congr
        by_cases h_top : derivAtTop f = ⊤
        · simp only [h_top, EReal.toReal_top, EReal.coe_zero, zero_mul, zero_add]
          rw [Measure.singularPart_eq_zero_of_ac (h3 h_top).1,
            Measure.singularPart_eq_zero_of_ac]
          · simp
          · rw [kernel.Measure.absolutelyContinuous_compProd_iff]
            exact h3 h_top
        lift (derivAtTop f) to ℝ using ⟨h_top, derivAtTop_ne_bot⟩ with df
        simp only [EReal.toReal_coe]
        rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _),
          ← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
        conv_rhs => rw [Measure.haveLebesgueDecomposition_add μ ν]
        rw [Measure.compProd_add_left, add_comm, Measure.singularPart_add]
        simp only [Measure.add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply]
        rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        simp only [EReal.coe_add]
        norm_cast
        rw [mul_add]
        congr
        rw [singularPart_compProd]
        simp only [Measure.add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply]
        rw [Measure.compProd_apply MeasurableSet.univ]
        rw [Measure.compProd_apply MeasurableSet.univ]
        simp only [Measure.singularPart_singularPart, Set.preimage_univ]
        rw [← lintegral_add_right]
        · rw [← lintegral_one]
          congr with a
          have h : κ a Set.univ = 1 := by simp
          rw [← kernel.rnDeriv_add_singularPart κ η] at h
          simp only [kernel.coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure,
            OuterMeasure.coe_add] at h
          exact h.symm
        · exact kernel.measurable_coe _ MeasurableSet.univ

/-- Composition of a measure and a kernel.

Defined using `MeasureTheory.Measure.bind` -/
scoped[ProbabilityTheory] infixl:100 " ∘ₘ " => MeasureTheory.Measure.bind

lemma Measure.comp_eq_snd_compProd (μ : Measure α) [SFinite μ]
    (κ : kernel α β) [IsSFiniteKernel κ] :
    μ ∘ₘ κ = (μ ⊗ₘ κ).snd := by
  ext s hs
  rw [Measure.bind_apply hs (kernel.measurable _), Measure.snd_apply hs,
    Measure.compProd_apply]
  · rfl
  · exact measurable_snd hs

lemma fDiv_fst_le [Nonempty β] [StandardBorelSpace β]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) :
    fDiv f μ.fst ν.fst ≤ fDiv f μ ν := by
  rw [← Measure.compProd_fst_condKernel μ, ← Measure.compProd_fst_condKernel ν, kernel.Measure.fst_compProd,
    kernel.Measure.fst_compProd]
  exact le_fDiv_compProd μ.fst ν.fst μ.condKernel ν.condKernel hf hf_cvx hf_cont

lemma _root_.MeasureTheory.Measure.fst_map_swap (μ : Measure (α × β)) :
    (μ.map Prod.swap).fst = μ.snd := by
    ext s hs
    rw [Measure.fst, Measure.map_map measurable_fst measurable_swap, Measure.snd_apply hs,
      Measure.map_apply (measurable_fst.comp measurable_swap) hs]
    congr

lemma fDiv_snd_le [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) :
    fDiv f μ.snd ν.snd ≤ fDiv f μ ν := by
  rw [← μ.fst_map_swap, ← ν.fst_map_swap]
  refine (fDiv_fst_le _ _ hf hf_cvx hf_cont).trans_eq ?_
  exact fDiv_map_measurableEmbedding MeasurableEquiv.prodComm.measurableEmbedding

lemma fDiv_comp_le_compProd [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) :
    fDiv f (μ ∘ₘ κ) (ν ∘ₘ η) ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simp_rw [Measure.comp_eq_snd_compProd]
  exact fDiv_snd_le _ _ hf hf_cvx hf_cont

lemma fDiv_comp_left_le [Nonempty α] [StandardBorelSpace α]
    [MeasurableSpace.CountablyGenerated β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) :
    fDiv f (μ ∘ₘ κ) (μ ∘ₘ η) ≤ condFDiv f κ η μ := by
  calc fDiv f (μ ∘ₘ κ) (μ ∘ₘ η)
    ≤ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) := fDiv_comp_le_compProd μ μ κ η hf hf_cvx hf_cont
  _ = condFDiv f κ η μ := fDiv_compProd_left μ κ η hf hf_cvx

lemma fDiv_comp_right_le [Nonempty α] [StandardBorelSpace α]
    [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : kernel α β) [IsMarkovKernel κ]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) :
    fDiv f (μ ∘ₘ κ) (ν ∘ₘ κ) ≤ fDiv f μ ν := by
  calc fDiv f (μ ∘ₘ κ) (ν ∘ₘ κ)
    ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) := fDiv_comp_le_compProd μ ν κ κ hf hf_cvx hf_cont
  _ = fDiv f μ ν := fDiv_compProd_right μ ν κ hf hf_cvx

end ProbabilityTheory

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import TestingLowerBounds.Convex
public import TestingLowerBounds.ForMathlib.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Composition-products of measures and kernels: singular parts and integrability

## Main statements

* `singularPart_compProd_left`, `singularPart_compProd_right`, `singularPart_compProd`: singular
  part of `μ ⊗ₘ κ` with respect to `ν ⊗ₘ η`.
* `lintegral_singularPart`, `lintegral_rnDeriv_mul_singularPart`: integrals of the singular parts
  of kernels, written as singular parts of composition-products.
* `integrable_f_rnDeriv_compProd_iff`: integrability of `f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x)` in terms of the
  integrability of its sections.

-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : ℝ → ℝ}

section SingularPart

lemma singularPart_compProd_left (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsFiniteKernel κ] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ κ) = μ.singularPart ν ⊗ₘ κ := by
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν, Measure.compProd_add_left,
    Measure.singularPart_add]
  have : (ν.withDensity (∂μ/∂ν) ⊗ₘ κ).singularPart (ν ⊗ₘ κ) = 0 := by
    refine Measure.singularPart_eq_zero_of_ac (Measure.AbsolutelyContinuous.compProd ?_ ?_)
    · exact withDensity_absolutelyContinuous _ _
    · exact ae_of_all _ fun _ ↦ by rfl
  rw [this, add_zero]
  rw [Measure.singularPart_eq_self]
  refine Measure.MutuallySingular.compProd_of_left ?_ κ κ
  exact Measure.mutuallySingular_singularPart _ _

private lemma lintegral_apply_prodMk_preimage {f : α → Set β → ℝ≥0∞} (hf : ∀ a, f a ∅ = 0)
    {s : Set α} (hs : MeasurableSet s) (t : Set β) :
    ∫⁻ a, f a (Prod.mk a ⁻¹' s ×ˢ t) ∂μ = ∫⁻ a in s, f a t ∂μ := by
  rw [← lintegral_indicator hs _]
  congr with a
  classical
  rw [Set.indicator_apply]
  split_ifs with ha <;> simp [ha, hf]

variable [CountableOrCountablyGenerated α β]

lemma singularPart_compProd'' (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ η.withDensity (κ.rnDeriv η) + μ.singularPart ν ⊗ₘ κ.singularPart η
        + ν.withDensity (∂μ/∂ν) ⊗ₘ κ.singularPart η := by
  conv_lhs => rw [← κ.rnDeriv_add_singularPart η, Measure.compProd_add_right,
    μ.haveLebesgueDecomposition_add ν]
  simp_rw [Measure.compProd_add_left, Measure.singularPart_add]
  have : (ν.withDensity (∂μ/∂ν) ⊗ₘ η.withDensity (κ.rnDeriv η)).singularPart (ν ⊗ₘ η) = 0 := by
    refine Measure.singularPart_eq_zero_of_ac (Measure.AbsolutelyContinuous.compProd ?_ ?_)
    · exact withDensity_absolutelyContinuous _ _
    · exact ae_of_all _ (Kernel.withDensity_absolutelyContinuous _)
  rw [this, add_zero, ← add_assoc]
  congr
  · rw [Measure.singularPart_eq_self]
    exact Measure.MutuallySingular.compProd_of_left (μ.mutuallySingular_singularPart ν)
      (η.withDensity (κ.rnDeriv η)) η
  · rw [Measure.singularPart_eq_self]
    exact Measure.MutuallySingular.compProd_of_left (μ.mutuallySingular_singularPart ν)
      (κ.singularPart η) η
  · rw [Measure.singularPart_eq_self]
    exact Measure.MutuallySingular.compProd_of_right (ν.withDensity (∂μ/∂ν)) ν
      (.of_forall <| κ.mutuallySingular_singularPart _)

lemma singularPart_compProd (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ η.withDensity (κ.rnDeriv η) + μ ⊗ₘ κ.singularPart η := by
  rw [singularPart_compProd'']
  have : (μ ⊗ₘ κ.singularPart η) = (μ.singularPart ν ⊗ₘ κ.singularPart η)
        + (ν.withDensity (∂μ/∂ν) ⊗ₘ κ.singularPart η) := by
    rw [← Measure.compProd_add_left, ← μ.haveLebesgueDecomposition_add ν]
  rw [this]
  abel

lemma singularPart_compProd' (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ κ + ν.withDensity (∂μ/∂ν) ⊗ₘ κ.singularPart η := by
  rw [singularPart_compProd'']
  have : μ.singularPart ν ⊗ₘ κ
      = μ.singularPart ν ⊗ₘ η.withDensity (κ.rnDeriv η) + μ.singularPart ν ⊗ₘ κ.singularPart η := by
    rw [← Measure.compProd_add_right, (κ.rnDeriv_add_singularPart η)]
  rw [this]

lemma singularPart_compProd_right (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) = μ ⊗ₘ κ.singularPart η := by
  rw [singularPart_compProd, Measure.singularPart_self, Measure.compProd_zero_left, zero_add]

lemma setLIntegral_rnDeriv_mul_singularPart
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a in s, (∂μ/∂ν) a * (κ a).singularPart (η a) t ∂ν
      = ((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) (s ×ˢ t) := by
  rw [singularPart_compProd', Measure.coe_add, Pi.add_apply, Measure.compProd_apply (hs.prod ht),
    Measure.compProd_apply (hs.prod ht), lintegral_apply_prodMk_preimage (by simp) hs,
    lintegral_apply_prodMk_preimage (by simp) hs, ν.singularPart_withDensity]
  simp only [Measure.restrict_zero, lintegral_zero_measure, zero_add]
  have : ν.withDensity (∂ν.withDensity (∂μ/∂ν)/∂ν) = ν.withDensity (∂μ/∂ν) :=
    withDensity_congr_ae (ν.rnDeriv_withDensity (μ.measurable_rnDeriv _))
  rw [this, ← setLIntegral_rnDeriv_mul (μ := ν.withDensity (∂μ/∂ν)) (ν := ν)
    (withDensity_absolutelyContinuous _ _) (Kernel.measurable_coe _ ht).aemeasurable hs]
  refine setLIntegral_congr_fun_ae hs ?_
  filter_upwards [ν.rnDeriv_withDensity (μ.measurable_rnDeriv ν)] with x hx _
  rw [hx, Kernel.singularPart_eq_singularPart_measure]

lemma lintegral_rnDeriv_mul_singularPart (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a, (∂μ/∂ν) a * (κ a).singularPart (η a) t ∂ν
      = ((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) (.univ ×ˢ t) := by
  rw [← setLIntegral_rnDeriv_mul_singularPart _ _ _ _ .univ ht, setLIntegral_univ]

lemma setLIntegral_singularPart (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ a in s, (κ a).singularPart (η a) t ∂μ = (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) (s ×ˢ t) := by
  rw [singularPart_compProd_right, Measure.compProd_apply (hs.prod ht)]
  simp only [Kernel.singularPart_eq_singularPart_measure]
  rw [lintegral_apply_prodMk_preimage (fun _ ↦ by simp) hs]

lemma lintegral_singularPart (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ a, (κ a).singularPart (η a) s ∂μ = (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) (.univ ×ˢ s) := by
  rw [← setLIntegral_univ, setLIntegral_singularPart _ _ _ .univ hs]

/-- Replacing `κ` by the absolutely continuous part `η.withDensity (κ.rnDeriv η)` does not change
the Radon-Nikodym derivative of `μ ⊗ₘ κ` with respect to `ν ⊗ₘ η`. -/
lemma rnDeriv_measure_compProd_withDensity_rnDeriv (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (∂μ ⊗ₘ (η.withDensity (κ.rnDeriv η))/∂ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) := by
  let κ' := η.withDensity (κ.rnDeriv η)
  have h_ae : ∀ᵐ p ∂(ν ⊗ₘ η), κ'.rnDeriv η p.1 p.2 = κ.rnDeriv η p.1 p.2 := by
    refine Kernel.ENNReal.ae_eq_compProd_of_forall_ae_eq ν η ?_ ?_ ?_
    · exact κ'.measurable_rnDeriv _
    · exact κ.measurable_rnDeriv _
    · exact fun a ↦ η.rnDeriv_withDensity (κ.measurable_rnDeriv _) a
  filter_upwards [rnDeriv_measure_compProd μ ν κ η,
      rnDeriv_measure_compProd μ ν κ' η, h_ae] with p h1 h2 h3
  rw [h1, h2, h3]

end SingularPart

section Integrable

variable {E : Type*}

-- todo find better name
theorem _root_.MeasureTheory.Integrable.compProd_mk_left_ae' [NormedAddCommGroup E]
    [SFinite μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ ⊗ₘ κ)) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ f (x, y)) (κ x) := by
  rw [Measure.compProd] at hf
  simpa using hf.ae_of_compProd

theorem _root_.MeasureTheory.Integrable.integral_norm_compProd' [NormedAddCommGroup E]
    [SFinite μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun x ↦ ∫ y, ‖f (x, y)‖ ∂(κ x)) μ := by
  rw [Measure.compProd] at hf
  simpa using hf.integral_norm_compProd

theorem _root_.MeasureTheory.Integrable.integral_compProd' [NormedAddCommGroup E]
    [SFinite μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄ [NormedSpace ℝ E]
    (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun x ↦ ∫ y, f (x, y) ∂(κ x)) μ := by
  rw [Measure.compProd] at hf
  simpa using hf.integral_compProd

lemma integrable_f_rnDeriv_compProd_iff_of_nonneg' [IsFiniteMeasure ν]
    [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η)
      ↔ (∀ᵐ a ∂ν, Integrable (fun x ↦ f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, x)).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, b)).toReal ∂(η a)) ν := by
  have h_ae : AEStronglyMeasurable (fun x ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η) :=
    (hf.comp_measurable (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
  · have h_int := h.integral_compProd'
    rw [Measure.integrable_compProd_iff h_ae] at h
    exact ⟨h.1, h_int⟩
  · rw [Measure.integrable_compProd_iff h_ae]
    refine ⟨h1, ?_⟩
    convert h2 using 4 with a b
    rw [norm_of_nonneg]
    exact h_nonneg _ ENNReal.toReal_nonneg

lemma integrable_add_affine_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : ℝ → ℝ) (a b : ℝ) :
    Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal + a * (μ.rnDeriv ν x).toReal + b) ν
      ↔ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν := by
  have h_int : Integrable (fun x ↦ a * (μ.rnDeriv ν x).toReal + b) ν :=
    (Measure.integrable_toReal_rnDeriv.const_mul _).add (integrable_const _)
  simp_rw [add_assoc]
  change Integrable ((fun x ↦ f ((∂μ/∂ν) x).toReal) + (fun x ↦ (a * ((∂μ/∂ν) x).toReal + b))) ν ↔ _
  rwa [integrable_add_iff_integrable_left]

lemma integrable_sub_affine_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : ℝ → ℝ) (a b : ℝ) :
    Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal - (a * (μ.rnDeriv ν x).toReal + b)) ν
      ↔ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν := by
  simp_rw [sub_eq_add_neg, neg_add, ← neg_mul, ← add_assoc]
  rw [integrable_add_affine_iff f]

lemma integrable_f_rnDeriv_compProd_iff' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η)
      ↔ (∀ᵐ a ∂ν, Integrable (fun x ↦ f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, x)).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, b)).toReal ∂(η a)) ν := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, _ → c * x + c' ≤ f x := h_cvx.exists_affine_le (convex_Ici 0)
  simp only [Set.mem_Ici] at h
  rw [← integrable_sub_affine_iff f c c']
  change Integrable (fun x ↦
    (fun y ↦ f y - (c * y + c')) ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η) ↔ _
  rw [integrable_f_rnDeriv_compProd_iff_of_nonneg' (f := fun y ↦ f y - (c * y + c'))]
  rotate_left
  · exact hf.sub ((stronglyMeasurable_id.const_mul c).add_const c')
  · simpa using h
  have h_int' : Integrable (fun p ↦ ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) p).toReal) (ν ⊗ₘ η) :=
    Measure.integrable_toReal_rnDeriv
  rw [Measure.integrable_compProd_iff] at h_int'
  swap; · exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.aestronglyMeasurable
  have h_int''' : ∀ᵐ a ∂ν,
      Integrable (fun x ↦ c * ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, x)).toReal + c') (η a) := by
    filter_upwards [h_int'.1] with a h_int''
    exact ((h_int''.const_mul _).add (integrable_const _))
  -- The goal has shape `(P₁ ∧ Q₁) ↔ (P₂ ↔ Q₂)`. We prove first `P₁ ↔ P₂`.
  have h_left : (∀ᵐ a ∂ν, Integrable (fun x ↦ f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, x)).toReal
        - (c * (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, x)).toReal + c')) (η a))
      ↔ ∀ᵐ a ∂ν, Integrable (fun x ↦ f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, x)).toReal) (η a) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · filter_upwards [h, h_int'''] with a h h_int'''
      change Integrable ((fun x ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, x)).toReal)
        + (fun x ↦ -(c * ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, x)).toReal + c'))) (η a) at h
      rwa [integrable_add_iff_integrable_left h_int'''.fun_neg] at h
    · filter_upwards [h, h_int'''] with a h h_int'''
      simp_rw [sub_eq_add_neg]
      rwa [integrable_add_iff_integrable_left' h_int'''.fun_neg]
  rw [h_left, and_congr_right_iff]
  -- Now we have proved `P₁ ↔ P₂` and it remains to prove `P₂ → (Q₁ ↔ Q₂)`.
  intro h_int
  have : ∀ᵐ a ∂ν, ∫ b, f (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, b)).toReal
        - (c * (((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η)) (a, b)).toReal + c') ∂η a
      = ∫ b, f ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (a, b)).toReal ∂η a
        - ∫ b, c * ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (a, b)).toReal + c' ∂η a := by
    filter_upwards [h_int, h_int'''] with a h_int h_int'''
    rw [← integral_sub h_int h_int''']
  rw [integrable_congr this]
  simp_rw [sub_eq_add_neg]
  rw [integrable_add_iff_integrable_left']
  -- `⊢ Integrable (fun x ↦ -∫ (b : β), c * ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (x, b)).toReal + c' ∂η x) ν`
  have h_int_compProd :
      Integrable (fun x ↦ ∫ b, ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (x, b)).toReal ∂η x) ν := by
    convert h_int'.2 with a b
    rw [norm_of_nonneg ENNReal.toReal_nonneg]
  have : ∀ᵐ x ∂ν, -∫ b, c * ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (x, b)).toReal + c' ∂η x
      = -c * ∫ b, ((∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) (x, b)).toReal ∂η x
        - c' * (η x .univ).toReal := by
    filter_upwards [h_int'.1] with x h_int'
    rw [integral_add _ (integrable_const _)]
    swap; · exact h_int'.const_mul _
    simp only [integral_const, smul_eq_mul, neg_add_rev, neg_mul]
    rw [add_comm, mul_comm]
    congr 1
    rw [mul_comm c, ← smul_eq_mul, ← integral_smul_const]
    simp_rw [smul_eq_mul, mul_comm _ c]
  rw [integrable_congr this]
  refine Integrable.sub (h_int_compProd.const_mul _) (Integrable.const_mul ?_ _)
  simp_rw [← measureReal_def, ← integral_indicator_one MeasurableSet.univ]
  simp only [Set.mem_univ, Set.indicator_of_mem, Pi.one_apply]
  exact Integrable.integral_compProd' (f := fun _ ↦ 1) (integrable_const _)

lemma integrable_f_rnDeriv_compProd_iff'_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η)
    (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η)
      ↔ (∀ᵐ a ∂ν,
        Integrable (fun x ↦ f (μ.rnDeriv ν a * ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η)) (a, x)).toReal) (η a))
      ∧ Integrable (fun a ↦
        ∫ b, f (μ.rnDeriv ν a * ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η)) (a, b)).toReal ∂(η a)) ν := by
  rw [integrable_f_rnDeriv_compProd_iff' hf h_cvx]
  congr! 1
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    all_goals
    · filter_upwards [Kernel.rnDeriv_compProd' h_ac ν, h] with a ha h
      refine (integrable_congr ?_).mp h
      filter_upwards [ha] with b hb
      rw [hb]
  · refine integrable_congr ?_
    filter_upwards [Kernel.rnDeriv_compProd' h_ac ν] with a ha
    refine integral_congr_ae ?_
    filter_upwards [ha] with b hb
    rw [hb]

lemma f_compProd_congr_left (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsFiniteKernel κ] :
    ∀ᵐ a ∂ν, (fun b ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ κ) (a, b)).toReal)
      =ᵐ[κ a] fun _ ↦ f ((∂μ/∂ν) a).toReal := by
  have h_eq_compProd := Kernel.rnDeriv_measure_compProd_left' μ ν κ
  filter_upwards [h_eq_compProd] with a ha
  filter_upwards [ha] with b hb
  rw [hb]

lemma integral_f_compProd_left_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsFiniteKernel κ] :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ κ) (a, b)).toReal ∂(κ a))
      =ᵐ[ν] fun a ↦ (κ a .univ).toReal * f ((∂μ/∂ν) a).toReal := by
  filter_upwards [f_compProd_congr_left μ ν κ] with a ha
  rw [integral_congr_ae ha]
  simp [measureReal_def]

lemma integrable_f_rnDeriv_compProd_left_iff' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) x).toReal) (ν ⊗ₘ κ)
      ↔ Integrable (fun a ↦ (κ a .univ).toReal * f ((∂μ/∂ν) a).toReal) ν := by
  rw [integrable_f_rnDeriv_compProd_iff' hf h_cvx,
    integrable_congr (integral_f_compProd_left_congr μ ν κ)]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  filter_upwards [f_compProd_congr_left (f := f) μ ν κ] with x hx
  rw [integrable_congr hx]
  exact integrable_const _

lemma integrable_f_rnDeriv_compProd_left_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) x).toReal) (ν ⊗ₘ κ)
      ↔ Integrable (fun a ↦ f ((∂μ/∂ν) a).toReal) ν := by
  rw [integrable_f_rnDeriv_compProd_left_iff' hf h_cvx]
  simp

variable [CountableOrCountablyGenerated α β]

lemma f_compProd_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂ν, (fun b ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal)
      =ᵐ[η a] fun b ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal := by
  have h_eq_compProd := Kernel.rnDeriv_measure_compProd' μ ν κ η
  filter_upwards [h_eq_compProd] with a ha
  filter_upwards [ha] with b hb
  rw [hb]

lemma integral_f_compProd_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a))
      =ᵐ[ν] fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a) := by
  filter_upwards [f_compProd_congr μ ν κ η] with a ha using integral_congr_ae ha

lemma integral_f_compProd_right_congr (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b)).toReal ∂(η a))
      =ᵐ[μ] fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a) := by
  filter_upwards [integral_f_compProd_congr μ μ κ η, μ.rnDeriv_self] with a ha h_eq_one
  rw [ha]
  simp_rw [h_eq_one, one_mul]

lemma integrable_f_rnDeriv_of_integrable_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)) :
    ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((κ a).rnDeriv (η a) x).toReal) (η a) := by
  rw [Measure.integrable_compProd_iff] at hf_int
  swap
  · exact (hf.comp_measurable (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
  have h := Kernel.rnDeriv_measure_compProd_right' μ κ η
  filter_upwards [h, hf_int.1] with a ha1 ha2
  refine (integrable_congr ?_).mp ha2
  filter_upwards [ha1] with b hb
  rw [hb]

lemma integrable_f_rnDeriv_compProd_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η)
      ↔ (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a)) ν := by
  have h_ae_eq : ∀ᵐ a ∂ν, (fun y ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, y)).toReal)
      =ᵐ[η a] fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal := f_compProd_congr μ ν κ η
  rw [integrable_f_rnDeriv_compProd_iff' hf h_cvx]
  congr! 1
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · filter_upwards [h_ae_eq, h] with a ha h
      rwa [integrable_congr ha.symm]
    · filter_upwards [h_ae_eq, h] with a ha h
      rwa [integrable_congr ha]
  · refine integrable_congr ?_
    filter_upwards [h_ae_eq] with a ha
    exact integral_congr_ae ha

lemma integrable_f_rnDeriv_compProd_right_iff [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)
      ↔ (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a)) μ := by
  rw [integrable_f_rnDeriv_compProd_iff hf h_cvx]
  have h_one := μ.rnDeriv_self
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩⟩
  · filter_upwards [h1, h_one] with a ha1 ha2
    simpa [ha2] using ha1
  · refine (integrable_congr ?_).mpr h2
    filter_upwards [h_one] with a ha
    simp [ha]
  · filter_upwards [h1, h_one] with a ha1 ha2
    simpa [ha2] using ha1
  · refine (integrable_congr ?_).mpr h2
    filter_upwards [h_one] with a ha
    simp [ha]

end Integrable


end ProbabilityTheory

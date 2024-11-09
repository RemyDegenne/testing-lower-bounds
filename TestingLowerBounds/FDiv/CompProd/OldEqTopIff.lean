/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import TestingLowerBounds.FDiv.Basic
import TestingLowerBounds.FDiv.IntegralRnDerivSingularPart
import TestingLowerBounds.MeasureCompProd
/-!

-/

open Real MeasureTheory Filter MeasurableSpace Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : ℝ → ℝ}

lemma f_rnDeriv_ae_le_integral'' [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    (fun a ↦ f ((∂μ/∂ν) a * κ a .univ).toReal)
      ≤ᵐ[ν] fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a) := by
  have h_compProd := Kernel.rnDeriv_measure_compProd' μ ν κ η
  have h_lt_top := Measure.ae_ae_of_ae_compProd <| (μ ⊗ₘ κ).rnDeriv_lt_top (ν ⊗ₘ η)
  have := Measure.integrable_toReal_rnDeriv (μ := μ ⊗ₘ κ) (ν := ν ⊗ₘ η)
  rw [Measure.integrable_compProd_iff] at this
  swap
  · refine (Measurable.stronglyMeasurable ?_).aestronglyMeasurable
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hκη' : ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → κ a ≪ η a := Measure.ae_rnDeriv_ne_zero_imp_of_ae hκη
  filter_upwards [hκη', h_compProd, h_lt_top, h_int.compProd_mk_left_ae', this.1]
    with a h_ac h_eq h_lt_top h_int' h_rnDeriv_int
  calc f ((∂μ/∂ν) a * κ a .univ).toReal
    = f ((∂μ/∂ν) a * ∫⁻ b, (∂κ a/∂η a) b ∂η a).toReal := by
        by_cases h0 : (∂μ/∂ν) a = 0
        · simp [h0]
        · rw [Measure.lintegral_rnDeriv (h_ac h0)]
  _ = f (∫⁻ b,(∂μ/∂ν) a * (∂κ a/∂η a) b ∂η a).toReal := by
        rw [lintegral_const_mul _ ((κ a).measurable_rnDeriv _)]
  _ = f (∫⁻ b, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b) ∂η a).toReal := by rw [lintegral_congr_ae h_eq]
  _ = f (∫ b, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a) := by
        rw [integral_toReal _ h_lt_top]
        exact ((Measure.measurable_rnDeriv _ _).comp measurable_prod_mk_left).aemeasurable
  _ ≤ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a := by
        rw [← average_eq_integral, ← average_eq_integral]
        exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp) h_rnDeriv_int h_int'

lemma integrable_f_rnDeriv_mul_kernel'' [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun a ↦ f ((∂μ/∂ν) a * κ a .univ).toReal) ν := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun a ↦ f ((∂μ/∂ν) a * κ a .univ).toReal)
    (g₁ := fun x ↦ c * ((∂μ/∂ν) x * κ x .univ).toReal + c')
    (g₂ := fun x ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (x, b)).toReal ∂(η x))
    ?_ ?_ ?_ ?_ ?_
  · exact (hf.comp_measurable ((μ.measurable_rnDeriv _).mul
      (κ.measurable_coe .univ)).ennreal_toReal).aestronglyMeasurable
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_ae_le_integral'' μ ν κ η hf_cvx hf_cont h_int hκη
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    simp_rw [ENNReal.toReal_mul]
    have h := integrable_rnDeriv_mul_withDensity μ ν κ η
    have h_ae : ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → η.withDensity (κ.rnDeriv η) a = κ a := by
      refine Measure.ae_rnDeriv_ne_zero_imp_of_ae ?_
      filter_upwards [hκη] with x hx
      rw [Kernel.withDensity_rnDeriv_eq hx]
    refine (integrable_congr ?_).mp h
    filter_upwards [h_ae] with x hx
    by_cases h0 : (∂μ/∂ν) x = 0
    · simp [h0]
    · rw [hx h0]
  · exact h_int.integral_compProd'

lemma integrable_f_rnDeriv_mul_withDensity'' [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η)) :
    Integrable (fun a ↦
      f ((∂μ/∂ν) a * η.withDensity (κ.rnDeriv η) a .univ).toReal) ν := by
  refine integrable_f_rnDeriv_mul_kernel'' μ ν _ η hf hf_cvx hf_cont ?_ ?_
  · refine (integrable_congr ?_).mp h_int
    filter_upwards [Measure.rnDeriv_measure_compProd_Kernel_withDensity μ ν κ η] with x hx
    rw [hx]
  · exact ae_of_all _ (fun _ ↦ Kernel.withDensity_absolutelyContinuous _ _)

lemma f_rnDeriv_le_add'' [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsFiniteKernel η]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (h_deriv : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∀ᵐ a ∂ ν, f ((∂μ/∂ν) a).toReal
      ≤ f ((∂μ/∂ν) a * η.withDensity (κ.rnDeriv η) a .univ).toReal
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal * (κ.singularPart η a .univ).toReal := by
  by_cases h_deriv_top : derivAtTop f = ⊤
  · simp only [ENNReal.toReal_mul, h_deriv_top, EReal.toReal_top, zero_mul, add_zero]
    have h_ae : ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → η.withDensity (κ.rnDeriv η) a = κ a := by
      refine Measure.ae_rnDeriv_ne_zero_imp_of_ae ?_
      filter_upwards [h_deriv h_deriv_top] with a ha_ac
      rw [Kernel.withDensity_rnDeriv_eq ha_ac]
    filter_upwards [h_ae] with a ha
    by_cases h0 : (∂μ/∂ν) a = 0
    · simp [h0]
    · rw [ha h0]
      simp
  refine ae_of_all _ (fun a ↦ ?_)
  simp only [ENNReal.toReal_mul]
  let κ' := η.withDensity (κ.rnDeriv η)
  calc f ((∂μ/∂ν) a).toReal
  _ ≤ f (((∂μ/∂ν) a).toReal * (κ' a .univ).toReal)
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal * (1 - (κ' a .univ).toReal) := by
      refine le_add_derivAtTop' hf_cvx h_deriv_top ENNReal.toReal_nonneg ENNReal.toReal_nonneg ?_
      calc (κ' a .univ).toReal
      _ ≤ (κ a .univ).toReal := by
          gcongr
          · exact measure_ne_top _ _
          · exact κ.withDensity_rnDeriv_le η a .univ
      _ = 1 := by simp
  _ = f (((∂μ/∂ν) a).toReal * (κ' a .univ).toReal)
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal * (κ.singularPart η a .univ).toReal := by
      congr
      norm_cast
      unfold_let κ'
      rw [sub_eq_iff_eq_add, ← ENNReal.one_toReal, ← measure_univ (μ := κ a)]
      conv_lhs => rw [← κ.rnDeriv_add_singularPart η, add_comm]
      simp only [Kernel.coe_add, Pi.add_apply, Measure.coe_add]
      rw [ENNReal.toReal_add]
      · exact measure_ne_top _ _
      · exact measure_ne_top _ _

lemma integrable_f_rnDeriv_of_integrable_compProd''' [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (hf_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (h_deriv : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun a ↦ f ((∂μ/∂ν) a).toReal)
    (g₁ := fun a ↦ c * ((∂μ/∂ν) a).toReal + c')
    (g₂ := fun a ↦ f ((∂μ/∂ν) a * η.withDensity (κ.rnDeriv η) a .univ).toReal
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal * (κ.singularPart η a .univ).toReal)
    ?_ ?_ ?_ ?_ ?_
  · exact (hf.comp_measurable (μ.measurable_rnDeriv _).ennreal_toReal).aestronglyMeasurable
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_le_add'' μ ν κ η hf_cvx h_deriv
  · exact (Measure.integrable_toReal_rnDeriv.const_mul _).add (integrable_const _)
  · refine Integrable.add ?_ ?_
    · exact integrable_f_rnDeriv_mul_withDensity'' μ ν κ η hf hf_cvx hf_cont hf_int
    · simp_rw [mul_assoc]
      refine Integrable.const_mul ?_ _
      simp_rw [Kernel.singularPart_eq_singularPart_measure]
      exact integrable_rnDeriv_mul_singularPart _ _ _ _

end ProbabilityTheory

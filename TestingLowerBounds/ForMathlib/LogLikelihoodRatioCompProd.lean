/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import TestingLowerBounds.CompProd

/-! # Log-likelihood ratio of composition-products

Integrability of the log-likelihood ratio of `μ ⊗ₘ κ` with respect to `ν ⊗ₘ η`, in terms of the
log-likelihood ratios of `μ` with respect to `ν` and of `κ a` with respect to `η a`
(`integrable_llr_compProd_iff`). Compare with Mathlib's
`InformationTheory.integrable_llr_compProd_iff`, which is stated with the log-likelihood ratio of
`μ ⊗ₘ κ` with respect to `μ ⊗ₘ η`.
-/

@[expose] public section

open Real MeasureTheory MeasurableSpace

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β}

lemma integrable_llr_compProd_of_integrable_llr [CountableOrCountablyGenerated α β]
    [IsMarkovKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (hμν : Integrable (llr μ ν) μ) (hκη_int : Integrable (fun a ↦ ∫ b, llr (κ a) (η a) b ∂(κ a)) μ)
    (hκη_ae : ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) :
    Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) := by
  rw [← integrable_rnDeriv_mul_log_iff h_ac]
  rw [integrable_f_rnDeriv_compProd_iff continuous_mul_log.stronglyMeasurable convexOn_mul_log]
  simp_rw [ENNReal.toReal_mul]
  have ⟨hμν_ac, hκη_ac⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  rw [Measure.absolutelyContinuous_compProd_right_iff] at hκη_ac
  have hμν_pos := Measure.rnDeriv_toReal_pos hμν_ac
  constructor
  · simp_rw [mul_assoc]
    apply Measure.ae_integrable_mul_rnDeriv_of_ae_integrable
    filter_upwards [hκη_ac, hκη_ae, hμν_pos] with a ha hκηa_ae hμν_pos
    have hμν_zero : ((∂μ/∂ν) a).toReal ≠ 0 := by linarith
    apply (integrable_rnDeriv_smul_iff ha).mpr (Integrable.congr _ _)
    · exact fun b ↦ log ((∂μ/∂ν) a).toReal + log ((∂κ a/∂η a) b).toReal
    swap
    · have hκη_pos := Measure.rnDeriv_toReal_pos ha
      filter_upwards [hκη_pos] with b hκη_pos
      have hκη_zero : ((∂κ a/∂η a) b).toReal ≠ 0 := by linarith
      rw [log_mul hμν_zero hκη_zero]
    exact Integrable.add (integrable_const _) ((llr_def _ _).symm ▸ hκηa_ae)
  · simp_rw [mul_assoc, integral_const_mul]
    apply (integrable_rnDeriv_smul_iff hμν_ac).mpr
    have h : (fun a ↦ log ((∂μ/∂ν) a).toReal + ∫ b, log ((∂κ a/∂η a) b).toReal ∂κ a)
        =ᵐ[μ] (fun a ↦ ∫ b, ((∂κ a/∂η a) b).toReal
          * log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) b).toReal) ∂η a) := by
      filter_upwards [hκη_ac, hμν_pos, hκη_ae] with a ha hμν_pos hκηa_ae
      have hμν_zero : ((∂μ/∂ν) a).toReal ≠ 0 := by linarith
      calc log ((∂μ/∂ν) a).toReal + ∫ b, log ((∂κ a/∂η a) b).toReal ∂κ a
        _ = ∫ b, log ((∂μ/∂ν) a).toReal + log ((∂κ a/∂η a) b).toReal ∂κ a := by
          rw [integral_add (integrable_const _)]
          · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
          · exact (llr_def _ _).symm ▸ hκηa_ae
        _ = ∫ b, log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) b).toReal) ∂κ a := by
          have hκη_pos := Measure.rnDeriv_toReal_pos ha
          apply integral_congr_ae
          filter_upwards [hκη_pos] with b hκη_pos
          have hκη_zero : ((∂κ a/∂η a) b).toReal ≠ 0 := by linarith
          rw [log_mul hμν_zero hκη_zero]
        _ = _ := (integral_rnDeriv_smul ha).symm
    refine Integrable.congr ((llr_def _ _ ▸ hμν).add ?_) h
    simp_rw [← llr_def]
    exact hκη_int

lemma ae_integrable_llr_of_integrable_llr_compProd [CountableOrCountablyGenerated α β]
    [IsMarkovKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a) := by
  have ⟨hμν_ac, hκη_ac⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  rw [Measure.absolutelyContinuous_compProd_right_iff] at hκη_ac
  have hμν_pos := Measure.rnDeriv_toReal_pos hμν_ac
  rw [← integrable_rnDeriv_mul_log_iff h_ac, integrable_f_rnDeriv_compProd_iff
    continuous_mul_log.stronglyMeasurable convexOn_mul_log] at h_int
  replace h_int := h_int.1
  simp_rw [ENNReal.toReal_mul, mul_assoc] at h_int
  apply Measure.ae_integrable_of_ae_integrable_mul_rnDeriv hμν_ac at h_int
  filter_upwards [h_int, hκη_ac, hμν_pos] with a h_int hκη_ac hμν_pos
  have hμν_zero : ((∂μ/∂ν) a).toReal ≠ 0 := by linarith
  have h : (fun b ↦ log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) b).toReal))
      =ᵐ[κ a] (fun b ↦ log (((∂μ/∂ν) a).toReal) + log (((∂κ a/∂η a) b).toReal)) := by
    have hκη_pos := Measure.rnDeriv_toReal_pos hκη_ac
    filter_upwards [hκη_pos] with b hκη_zero
    have hκη_zero : ((∂κ a/∂η a) b).toReal ≠ 0 := by linarith
    rw [log_mul hμν_zero hκη_zero]
  apply (integrable_rnDeriv_smul_iff hκη_ac).mp at h_int
  replace h_int := integrable_const_add_iff.mp  (Integrable.congr h_int h)
  exact (llr_def _ _).symm ▸ h_int

lemma integrable_integral_llr_of_integrable_llr_compProd [CountableOrCountablyGenerated α β]
    [IsMarkovKernel κ] [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    Integrable (fun a ↦ ∫ b, llr (κ a) (η a) b ∂(κ a)) μ := by
  have ⟨hμν_ac, hκη_ac⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  rw [Measure.absolutelyContinuous_compProd_right_iff] at hκη_ac
  have hμν_pos : ∀ᵐ a ∂μ, 0 < ((∂μ/∂ν) a).toReal := Measure.rnDeriv_toReal_pos hμν_ac
  have hμν_int : Integrable (fun a ↦ log ((∂μ/∂ν) a).toReal) μ := by
    rw [← llr_def]
    exact InformationTheory.integrable_llr_of_integrable_llr_compProd h_ac h_int
  have h : (fun a ↦ log ((∂μ/∂ν) a).toReal + ∫ b, log ((∂κ a/∂η a) b).toReal ∂κ a)
      =ᵐ[μ] (fun a ↦ ∫ b, ((∂κ a/∂η a) b).toReal
      * log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) b).toReal) ∂η a) := by
    filter_upwards [hκη_ac, hμν_pos, ae_integrable_llr_of_integrable_llr_compProd h_ac h_int]
      with a ha hμν_pos hκη_int
    have hμν_zero : ((∂μ/∂ν) a).toReal ≠ 0 := by linarith
    calc log ((∂μ/∂ν) a).toReal + ∫ b, log ((∂κ a/∂η a) b).toReal ∂κ a
      _ = ∫ b, log ((∂μ/∂ν) a).toReal + log ((∂κ a/∂η a) b).toReal ∂κ a := by
        rw [llr_def] at hκη_int
        rw [integral_add (integrable_const _) hκη_int]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      _ = ∫ b, log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) b).toReal) ∂κ a := by
        have hκη_pos := Measure.rnDeriv_toReal_pos ha
        apply integral_congr_ae
        filter_upwards [hκη_pos] with b hκη_pos
        have hκη_zero : ((∂κ a/∂η a) b).toReal ≠ 0 := by linarith
        rw [log_mul hμν_zero hκη_zero]
      _ = _ := (integral_rnDeriv_smul ha).symm
  rw [← integrable_rnDeriv_mul_log_iff h_ac] at h_int
  rw [integrable_f_rnDeriv_compProd_iff continuous_mul_log.stronglyMeasurable convexOn_mul_log]
    at h_int
  replace h_int := h_int.2
  simp_rw [ENNReal.toReal_mul, mul_assoc, integral_const_mul] at h_int
  apply (integrable_rnDeriv_smul_iff hμν_ac).mp at h_int
  replace h_int := (integrable_add_iff_integrable_right hμν_int).mp (Integrable.congr h_int h.symm)
  simp_rw [llr_def]
  exact h_int

lemma integrable_llr_compProd_iff [CountableOrCountablyGenerated α β] [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ↔ (Integrable (llr μ ν) μ
    ∧ Integrable (fun a ↦ ∫ b, llr (κ a) (η a) b ∂(κ a)) μ)
    ∧ ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a):=
  ⟨fun h ↦ ⟨⟨InformationTheory.integrable_llr_of_integrable_llr_compProd h_ac h,
    integrable_integral_llr_of_integrable_llr_compProd h_ac h⟩,
    ae_integrable_llr_of_integrable_llr_compProd h_ac h⟩,
    fun h ↦ integrable_llr_compProd_of_integrable_llr h_ac h.1.1 h.1.2 h.2⟩

end ProbabilityTheory

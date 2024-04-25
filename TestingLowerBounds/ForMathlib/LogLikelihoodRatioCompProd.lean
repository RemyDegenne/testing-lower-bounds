-- theorem foo (n : Nat) : 0 ≤ n := by exact? -- trick to make exact? work TODO : erase this when we are done

import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import TestingLowerBounds.FDiv.CondFDiv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TestingLowerBounds.ForMathlib.L1Space

open Real MeasureTheory MeasurableSpace

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
variable {μ ν : Measure α} {κ η : kernel α β}


lemma integrable_rnDeriv_mul_log_iff [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal) ν
      ↔ Integrable (llr μ ν) μ :=
  integrable_rnDeriv_smul_iff hμν

lemma integrable_llr_compProd_of_integrable_llr [CountablyGenerated β] [IsMarkovKernel κ]
    [IsFiniteKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_prod : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (hμν : Integrable (llr μ ν) μ) (hκη_int : Integrable (fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)) μ)
    (hκη_ae : ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) :
    Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) := by
  rw [← integrable_rnDeriv_mul_log_iff h_prod]
  rw [integrable_f_rnDeriv_compProd_iff (by measurability) Real.convexOn_mul_log]
  simp_rw [ENNReal.toReal_mul]
  have ⟨hμν_ac, hκη_ac⟩ := kernel.Measure.absolutelyContinuous_compProd_iff.mp h_prod
  have hμν_pos := Measure.rnDeriv_toReal_pos hμν_ac
  constructor
  · simp_rw [mul_assoc]
    apply Measure.ae_integrable_mul_rnDeriv_of_ae_integrable
    filter_upwards [hκη_ac, hκη_ae, hμν_pos] with a ha hκηa_ae hμν_pos
    have hμν_zero : ((∂μ/∂ν) a).toReal ≠ 0 := by linarith
    apply (MeasureTheory.integrable_rnDeriv_smul_iff ha).mpr
    apply Integrable.congr _ _
    · exact fun x ↦ log ((∂μ/∂ν) a).toReal + log ((∂κ a/∂η a) x).toReal
    swap
    · have hκη_pos := Measure.rnDeriv_toReal_pos ha
      filter_upwards [hκη_pos] with x hκη_pos
      have hκη_zero : ((∂κ a/∂η a) x).toReal ≠ 0 := by linarith
      rw [Real.log_mul hμν_zero hκη_zero]
    exact Integrable.add (integrable_const _) ((llr_def _ _).symm ▸ hκηa_ae)
  · simp_rw [mul_assoc, integral_mul_left]
    apply (MeasureTheory.integrable_rnDeriv_smul_iff hμν_ac).mpr
    have h : (fun a ↦ log ((∂μ/∂ν) a).toReal + ∫ x, log ((∂κ a/∂η a) x).toReal ∂κ a)
        =ᵐ[μ] (fun a ↦ ∫ x, ((∂κ a/∂η a) x).toReal
        * log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) x).toReal) ∂η a) := by
      filter_upwards [hκη_ac, hμν_pos, hκη_ae] with a ha hμν_pos hκηa_ae
      have hμν_zero : ((∂μ/∂ν) a).toReal ≠ 0 := by linarith
      calc
        _ = ∫ (x : β), log ((∂μ/∂ν) a).toReal + log ((∂κ a/∂η a) x).toReal ∂κ a := by
          rw [integral_add (integrable_const _)]
          · simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
          · exact (llr_def _ _).symm ▸ hκηa_ae
        _ = ∫ x, log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) x).toReal) ∂κ a := by
          have hκη_pos := Measure.rnDeriv_toReal_pos ha
          apply integral_congr_ae
          filter_upwards [hκη_pos] with x hκη_pos
          have hκη_zero : ((∂κ a/∂η a) x).toReal ≠ 0 := by linarith
          rw [Real.log_mul hμν_zero hκη_zero]
        _ = _ := (integral_rnDeriv_smul ha).symm
    apply Integrable.congr _ h
    apply Integrable.add
    · rw [← llr_def]
      exact hμν
    · simp_rw [← llr_def]
      exact hκη_int

lemma integrable_llr_of_integrable_llr_compProd [CountablyGenerated β] [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_prod : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    Integrable (llr μ ν) μ := by
  have ⟨hμν_ac, hκη_ac⟩ := kernel.Measure.absolutelyContinuous_compProd_iff.mp h_prod
  rw [← integrable_rnDeriv_mul_log_iff h_prod] at h_int
  replace h_int := integrable_f_rnDeriv_of_integrable_compProd' μ ν κ η (by measurability)
    Real.convexOn_mul_log Real.continuous_mul_log.continuousOn h_int (fun _ ↦ hκη_ac)
  exact (integrable_rnDeriv_mul_log_iff hμν_ac).mp h_int

lemma ae_integrable_llr_of_integrable_llr_compProd [CountablyGenerated β] [IsMarkovKernel κ]
    [IsFiniteKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_prod : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a) := by
  have ⟨hμν_ac, hκη_ac⟩ := kernel.Measure.absolutelyContinuous_compProd_iff.mp h_prod
  have hμν_pos := Measure.rnDeriv_toReal_pos hμν_ac
  rw [← integrable_rnDeriv_mul_log_iff h_prod] at h_int
  rw [integrable_f_rnDeriv_compProd_iff (by measurability) Real.convexOn_mul_log] at h_int
  replace h_int := h_int.1
  simp_rw [ENNReal.toReal_mul, mul_assoc] at h_int
  apply Measure.ae_integrable_of_ae_integrable_mul_rnDeriv hμν_ac at h_int
  filter_upwards [h_int, hκη_ac, hμν_pos] with a h_int hκη_ac hμν_pos
  have hμν_zero : ((∂μ/∂ν) a).toReal ≠ 0 := by linarith
  have h : (fun x ↦ log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) x).toReal))
      =ᵐ[κ a] (fun x ↦ log (((∂μ/∂ν) a).toReal) + log (((∂κ a/∂η a) x).toReal)) := by
    have hκη_pos := Measure.rnDeriv_toReal_pos hκη_ac
    filter_upwards [hκη_pos] with x hκη_zero
    have hκη_zero : ((∂κ a/∂η a) x).toReal ≠ 0 := by linarith
    rw [Real.log_mul hμν_zero hκη_zero]
  apply (MeasureTheory.integrable_rnDeriv_smul_iff hκη_ac).mp at h_int
  replace h_int := Integrable.integrable_const_add_iff.mp  (Integrable.congr h_int h)
  exact (llr_def _ _).symm ▸ h_int

lemma integrable_integral_llr_of_integrable_llr_compProd [CountablyGenerated β] [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_prod : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    Integrable (fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)) μ := by
  have ⟨hμν_ac, hκη_ac⟩ := kernel.Measure.absolutelyContinuous_compProd_iff.mp h_prod
  have hμν_pos := Measure.rnDeriv_toReal_pos hμν_ac
  have hμν_int : Integrable (fun a ↦ log ((∂μ/∂ν) a).toReal) μ := by
    rw [← llr_def]
    exact integrable_llr_of_integrable_llr_compProd h_prod h_int
  have h : (fun a ↦ log ((∂μ/∂ν) a).toReal + ∫ x, log ((∂κ a/∂η a) x).toReal ∂κ a)
      =ᵐ[μ] (fun a ↦ ∫ x, ((∂κ a/∂η a) x).toReal
      * log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) x).toReal) ∂η a) := by
    filter_upwards [hκη_ac, hμν_pos, ae_integrable_llr_of_integrable_llr_compProd h_prod h_int]
      with a ha hμν_pos hκη_int
    have hμν_zero : ((∂μ/∂ν) a).toReal ≠ 0 := by linarith
    calc
      _ = ∫ (x : β), log ((∂μ/∂ν) a).toReal + log ((∂κ a/∂η a) x).toReal ∂κ a := by
        rw [llr_def] at hκη_int
        rw [integral_add (integrable_const _) hκη_int]
        simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
      _ = ∫ x, log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) x).toReal) ∂κ a := by
        have hκη_pos := Measure.rnDeriv_toReal_pos ha
        apply integral_congr_ae
        filter_upwards [hκη_pos] with x hκη_pos
        have hκη_zero : ((∂κ a/∂η a) x).toReal ≠ 0 := by linarith
        rw [Real.log_mul hμν_zero hκη_zero]
      _ = _ := (integral_rnDeriv_smul ha).symm
  rw [← integrable_rnDeriv_mul_log_iff h_prod] at h_int
  rw [integrable_f_rnDeriv_compProd_iff (by measurability) Real.convexOn_mul_log] at h_int
  replace h_int := h_int.2
  simp_rw [ENNReal.toReal_mul, mul_assoc, integral_mul_left] at h_int
  apply (MeasureTheory.integrable_rnDeriv_smul_iff hμν_ac).mp at h_int
  replace h_int := (Integrable.integrable_add_iff_integrable_right hμν_int).mp (Integrable.congr h_int h.symm)
  simp_rw [llr_def]
  exact h_int

lemma integrable_llr_compProd_iff [CountablyGenerated β] [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_prod : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ↔ (Integrable (llr μ ν) μ
    ∧ Integrable (fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)) μ)
    ∧ ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a):= by
  constructor <;> intro h
  · exact ⟨⟨integrable_llr_of_integrable_llr_compProd h_prod h, integrable_integral_llr_of_integrable_llr_compProd h_prod h⟩,
      ae_integrable_llr_of_integrable_llr_compProd h_prod h⟩
  · exact integrable_llr_compProd_of_integrable_llr h_prod h.1.1 h.1.2 h.2

end ProbabilityTheory

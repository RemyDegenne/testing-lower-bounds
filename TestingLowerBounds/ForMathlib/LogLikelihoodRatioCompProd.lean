import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import TestingLowerBounds.FDiv.CompProd.CompProd
import TestingLowerBounds.FDiv.Measurable
import TestingLowerBounds.FDiv.CompProd.OldEqTopIff

open Real MeasureTheory MeasurableSpace

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β}

lemma integrable_rnDeriv_mul_log_iff [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    Integrable (fun a ↦ (μ.rnDeriv ν a).toReal * log (μ.rnDeriv ν a).toReal) ν
      ↔ Integrable (llr μ ν) μ :=
  integrable_rnDeriv_smul_iff hμν

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
  · simp_rw [mul_assoc, integral_mul_left]
    apply (integrable_rnDeriv_smul_iff hμν_ac).mpr
    have h : (fun a ↦ log ((∂μ/∂ν) a).toReal + ∫ b, log ((∂κ a/∂η a) b).toReal ∂κ a)
        =ᵐ[μ] (fun a ↦ ∫ b, ((∂κ a/∂η a) b).toReal
          * log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) b).toReal) ∂η a) := by
      filter_upwards [hκη_ac, hμν_pos, hκη_ae] with a ha hμν_pos hκηa_ae
      have hμν_zero : ((∂μ/∂ν) a).toReal ≠ 0 := by linarith
      calc log ((∂μ/∂ν) a).toReal + ∫ b, log ((∂κ a/∂η a) b).toReal ∂κ a
        _ = ∫ b, log ((∂μ/∂ν) a).toReal + log ((∂κ a/∂η a) b).toReal ∂κ a := by
          rw [integral_add (integrable_const _)]
          · simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
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

lemma integrable_llr_of_integrable_llr_compProd [CountableOrCountablyGenerated α β]
    [IsMarkovKernel κ] [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    Integrable (llr μ ν) μ := by
  have ⟨hμν_ac, hκη_ac⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  rw [← integrable_rnDeriv_mul_log_iff h_ac] at h_int
  replace h_int := integrable_f_rnDeriv_of_integrable_compProd''' μ ν κ η
    continuous_mul_log.stronglyMeasurable convexOn_mul_log continuous_mul_log.continuousOn h_int
    (fun _ ↦ hκη_ac)
  exact (integrable_rnDeriv_mul_log_iff hμν_ac).mp h_int

lemma ae_integrable_llr_of_integrable_llr_compProd [CountableOrCountablyGenerated α β]
    [IsMarkovKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a) := by
  have ⟨hμν_ac, hκη_ac⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
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
  have hμν_pos : ∀ᵐ a ∂μ, 0 < ((∂μ/∂ν) a).toReal := Measure.rnDeriv_toReal_pos hμν_ac
  have hμν_int : Integrable (fun a ↦ log ((∂μ/∂ν) a).toReal) μ := by
    rw [← llr_def]
    exact integrable_llr_of_integrable_llr_compProd h_ac h_int
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
        simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
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
  simp_rw [ENNReal.toReal_mul, mul_assoc, integral_mul_left] at h_int
  apply (integrable_rnDeriv_smul_iff hμν_ac).mp at h_int
  replace h_int := (integrable_add_iff_integrable_right hμν_int).mp (Integrable.congr h_int h.symm)
  simp_rw [llr_def]
  exact h_int

lemma integrable_llr_compProd_iff [CountableOrCountablyGenerated α β] [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ↔ (Integrable (llr μ ν) μ
    ∧ Integrable (fun a ↦ ∫ b, llr (κ a) (η a) b ∂(κ a)) μ)
    ∧ ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a):=
  ⟨fun h ↦ ⟨⟨integrable_llr_of_integrable_llr_compProd h_ac h,
    integrable_integral_llr_of_integrable_llr_compProd h_ac h⟩,
    ae_integrable_llr_of_integrable_llr_compProd h_ac h⟩,
    fun h ↦ integrable_llr_compProd_of_integrable_llr h_ac h.1.1 h.1.2 h.2⟩

lemma Kernel.integrable_llr_compProd_iff [CountableOrCountablyGenerated β γ]
    {κ₁ η₁ : Kernel α β} [IsFiniteKernel κ₁] [IsFiniteKernel η₁]
    {κ₂ η₂ : Kernel (α × β) γ} [IsMarkovKernel κ₂] [IsMarkovKernel η₂]
    (a : α) (h_ac : (κ₁ ⊗ₖ κ₂) a ≪ (η₁ ⊗ₖ η₂) a) :
    Integrable (llr ((κ₁ ⊗ₖ κ₂) a) ((η₁ ⊗ₖ η₂) a)) ((κ₁ ⊗ₖ κ₂) a)
      ↔ Integrable (llr (κ₁ a) (η₁ a)) (κ₁ a)
        ∧ Integrable (fun b ↦ ∫ x, (llr (κ₂ (a, b)) (η₂ (a, b)) x) ∂(κ₂ (a, b))) (κ₁ a)
        ∧ ∀ᵐ b ∂κ₁ a, Integrable (llr (κ₂ (a, b)) (η₂ (a, b))) (κ₂ (a, b)) := by
  simp_rw [Kernel.compProd_apply_eq_compProd_snd'] at h_ac
  simp_rw [Kernel.compProd_apply_eq_compProd_snd',
    ProbabilityTheory.integrable_llr_compProd_iff h_ac, Kernel.snd'_apply]
  by_cases h_int₁ : Integrable (llr (κ₁ a) (η₁ a)) (κ₁ a)
  swap; tauto
  by_cases h_int₂ : ∀ᵐ b ∂κ₁ a, Integrable (llr (κ₂ (a, b)) (η₂ (a, b))) (κ₂ (a, b))
  swap; tauto
  simp only [h_int₁, true_and, h_int₂, and_true]

/- this lemma actually doesn't pertain the compProd, but for now I am still leaving it here,
maybe when we put things in mathlib this could go in the basic file about llr,
or maybe it still needs to go in a separate file, since it needs the definition of kernel,
which now is not imported in the llr file -/
lemma measurableSet_integrable_llr [CountableOrCountablyGenerated α β]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | Integrable (fun b ↦ ((∂κ a/∂η a) b).toReal * llr (κ a) (η a) b) (η a)} := by
  simp_rw [llr_def]
  suffices MeasurableSet {a |
      Integrable (fun b ↦ (κ.rnDeriv η a b).toReal * log (κ.rnDeriv η a b).toReal) (η a)} by
    convert this using 3
    refine integrable_congr ?_
    filter_upwards [κ.rnDeriv_eq_rnDeriv_measure] with b hb
    rw [hb]
  refine measurableSet_kernel_integrable ?_
  exact continuous_mul_log.stronglyMeasurable.comp_measurable
    (κ.measurable_rnDeriv η).ennreal_toReal

lemma ae_compProd_integrable_llr_iff [CountableOrCountablyGenerated (α × β) γ] [SFinite μ]
    {ξ : Kernel α β} [IsSFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : ∀ᵐ (x : α × β) ∂μ ⊗ₘ ξ, κ x ≪ η x) :
    (∀ᵐ (x : α × β) ∂μ ⊗ₘ ξ, Integrable (llr (κ x) (η x)) (κ x))
      ↔ ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, Integrable (llr (κ (a, b)) (η (a, b))) (κ (a, b)) :=
  calc (∀ᵐ x ∂μ ⊗ₘ ξ, Integrable (llr (κ x) (η x)) (κ x))
  _ ↔ ∀ᵐ a ∂μ ⊗ₘ ξ, Integrable (fun x ↦ ((∂κ a/∂η a) x).toReal * llr (κ a) (η a) x) (η a) := by
    apply Filter.eventually_congr
    filter_upwards [h_ac] with a ha using (integrable_rnDeriv_smul_iff ha).symm
  _ ↔ ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, Integrable
      (fun x ↦ ((∂κ (a, b)/∂η (a, b)) x).toReal * llr (κ (a, b)) (η (a, b)) x) (η (a, b)) :=
    Kernel.ae_compProd_iff (measurableSet_integrable_llr κ η)
  _ ↔ ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, Integrable (llr (κ (a, b)) (η (a, b))) (κ (a, b)) := by
    apply Filter.eventually_congr
    rw [Measure.ae_compProd_iff (κ.measurableSet_absolutelyContinuous _)] at h_ac
    filter_upwards [h_ac] with a ha
    apply Filter.eventually_congr
    filter_upwards [ha] with b hb using (integrable_rnDeriv_smul_iff hb)

end ProbabilityTheory

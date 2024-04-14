/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import TestingLowerBounds.FDiv.CondFDiv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
/-!
# Kullback-Leibler divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

section move_this

lemma integrable_rnDeriv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν)
    [SigmaFinite μ] {f : α → E} (hf : Integrable f μ) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal • f x) ν :=
  (integrable_rnDeriv_smul_iff hμν).mpr hf

end move_this

open Classical in
/-- Kullback-Leibler divergence between two measures. -/
noncomputable def kl (μ ν : Measure α) : EReal :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ then ↑(∫ x, llr μ ν x ∂μ) else ⊤

lemma kl_of_ac_of_integrable (h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) :
    kl μ ν = ∫ x, llr μ ν x ∂μ := if_pos ⟨h1, h2⟩

@[simp]
lemma kl_of_not_ac (h : ¬ μ ≪ ν) : kl μ ν = ⊤ := if_neg (not_and_of_not_left _ h)

@[simp]
lemma kl_of_not_integrable (h : ¬ Integrable (llr μ ν) μ) : kl μ ν = ⊤ :=
  if_neg (not_and_of_not_right _ h)

lemma integrable_rnDeriv_mul_log_iff [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal) ν
      ↔ Integrable (llr μ ν) μ :=
  integrable_rnDeriv_smul_iff hμν

lemma derivAtTop_mul_log : derivAtTop (fun x ↦ x * log x) = ⊤ := by
  rw [derivAtTop_eq_top_iff]
  refine (tendsto_congr' ?_).mp tendsto_log_atTop
  simp only [EventuallyEq, eventually_atTop, ge_iff_le]
  refine ⟨1, fun x hx ↦ ?_⟩
  rw [mul_div_cancel_left₀ _ (zero_lt_one.trans_le hx).ne']

lemma fDiv_mul_log_eq_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv (fun x ↦ x * log x) μ ν = ⊤ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ := by
  rw [fDiv_eq_top_iff]
  simp only [derivAtTop_mul_log, true_and]
  by_cases hμν : μ ≪ ν
  · simp [hμν, integrable_rnDeriv_mul_log_iff hμν]
  · simp [hμν]

lemma kl_eq_fDiv [SigmaFinite μ] [SigmaFinite ν] :
    kl μ ν = fDiv (fun x ↦ x * log x) μ ν := by
  classical
  by_cases hμν : μ ≪ ν
  swap; · rw [fDiv_of_not_ac derivAtTop_mul_log hμν, kl_of_not_ac hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [fDiv_of_derivAtTop_eq_top derivAtTop_mul_log, kl_of_ac_of_integrable hμν h_int,
      if_pos ⟨(integrable_rnDeriv_mul_log_iff hμν).mpr h_int, hμν⟩]
    simp_rw [← smul_eq_mul]
    rw [integral_rnDeriv_smul hμν]
    rfl
  · rw [kl_of_not_integrable h_int, fDiv_of_not_integrable]
    rwa [integrable_rnDeriv_mul_log_iff hμν]

@[simp]
lemma kl_self (μ : Measure α) [SigmaFinite μ] : kl μ μ = 0 := by
  rw [kl_eq_fDiv, fDiv_self (by norm_num)]

lemma kl_eq_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    kl μ ν = ⊤ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ := by
  rw [kl_eq_fDiv, fDiv_mul_log_eq_top_iff]

section kl_nonneg

lemma kl_ne_bot (μ ν : Measure α) : kl μ ν ≠ ⊥ := by
  rw [kl]
  split_ifs with h
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
  · norm_num

lemma kl_ge_mul_log' [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (μ Set.univ).toReal * log (μ Set.univ).toReal ≤ kl μ ν :=
  (le_fDiv_of_ac Real.convexOn_mul_log Real.continuous_mul_log.continuousOn hμν).trans_eq
    kl_eq_fDiv.symm

lemma kl_ge_mul_log (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ Set.univ).toReal * log ((μ Set.univ).toReal / (ν Set.univ).toReal) ≤ kl μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [h_int]
  rw [kl_of_ac_of_integrable hμν h_int]
  norm_cast
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    apply? says exact Measure.measure_univ_eq_zero.mp (hμν rfl)
  let ν' := (ν Set.univ)⁻¹ • ν
  have : IsProbabilityMeasure ν' := by
    constructor
    simp only [ν', Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ENNReal.mul_inv_cancel]
    · simp [hν]
    · exact measure_ne_top _ _
  have hμν' : μ ≪ ν' := by
    refine Measure.AbsolutelyContinuous.trans hμν (Measure.absolutelyContinuous_smul ?_)
    simp [measure_ne_top ν]
  have h := kl_ge_mul_log' hμν'
  rw [kl_of_ac_of_integrable hμν', integral_congr_ae (llr_smul_right hμν (ν Set.univ)⁻¹ _ _)] at h
  rotate_left
  · simp [measure_ne_top ν _]
  · simp [hν]
  · rw [integrable_congr (llr_smul_right hμν (ν Set.univ)⁻¹ _ _)]
    rotate_left
    · simp [measure_ne_top ν _]
    · simp [hν]
    exact h_int.sub (integrable_const _)
  norm_cast at h
  rw [integral_sub h_int (integrable_const _), integral_const, smul_eq_mul, le_sub_iff_add_le,
    ENNReal.toReal_inv, log_inv, mul_neg, ← sub_eq_add_neg] at h
  rwa [log_div, mul_sub]
  · rw [ENNReal.toReal_ne_zero]
    simp [hμ, measure_ne_top μ]
  · rw [ENNReal.toReal_ne_zero]
    simp [hν, measure_ne_top ν]

lemma kl_nonneg (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ kl μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · rw [kl_of_not_ac hμν]; simp
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · rw [kl_of_not_integrable h_int]; simp
  calc 0
    = ((μ Set.univ).toReal : EReal) * log ((μ Set.univ).toReal / (ν Set.univ).toReal) := by simp
  _ ≤ kl μ ν := kl_ge_mul_log μ ν

lemma kl_eq_zero_iff [SigmaFinite μ] [SigmaFinite ν] : kl μ ν = 0 ↔ μ = ν := by
  constructor <;> intro h
  · by_cases hμν : μ ≪ ν
    swap; · rw [kl_of_not_ac hμν] at h; simp_all only [EReal.top_ne_zero]
    by_cases h_int : Integrable (llr μ ν) μ
    swap; · rw [kl_of_not_integrable h_int] at h; simp_all only [EReal.top_ne_zero]
    sorry -- TODO : decide what proof strategy to use here, maybe we could use the fact that jensen's inequality is an equality iff the function is constant a.e., but I don't know wether this is in mathlib
  · rw [h]
    exact kl_self ν

end kl_nonneg

section Conditional

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : kernel α β} {μ : Measure α}

open Classical in

/--
Kullback-Leibler divergence between two kernels κ and η conditional to a measure μ.
It is defined as KL(κ, η | μ) := ∫ x, KL(κ x, η x) dμ.
-/
noncomputable
def condKL (κ η : kernel α β) (μ : Measure α) : EReal :=
  if (∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤)
    ∧ (Integrable (fun x ↦ (kl (κ x) (η x)).toReal) μ)
  then ((μ[fun x ↦ (kl (κ x) (η x)).toReal] : ℝ) : EReal)
  else ⊤

lemma condKL_of_ae_finite_of_integrable (h1 : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤)
    (h2 : Integrable (fun x ↦ (kl (κ x) (η x)).toReal) μ) :
    condKL κ η μ = (μ[fun x ↦ (kl (κ x) (η x)).toReal] : ℝ) := if_pos ⟨h1, h2⟩

@[simp]
lemma condKL_of_not_ae_finite (h : ¬ (∀ᵐ x ∂μ, kl (κ x) (η x) ≠ ⊤)) :
    condKL κ η μ = ⊤ := if_neg (not_and_of_not_left _ h)

@[simp]
lemma condKL_of_not_ae_integrable (h : ¬ (∀ᵐ (a : α) ∂μ, Integrable (llr (κ a) (η a)) (κ a))) :
    condKL κ η μ = ⊤ := by
  apply condKL_of_not_ae_finite
  contrapose! h
  filter_upwards [h] with x hx
  contrapose! hx
  simp only [hx, ne_eq, not_false_eq_true, kl_of_not_integrable]

@[simp]
lemma condKL_of_not_ae_ac (h : ¬ (∀ᵐ x ∂μ, (κ x) ≪ (η x))) :
    condKL κ η μ = ⊤ := by
  apply condKL_of_not_ae_finite
  contrapose! h
  filter_upwards [h] with x hx
  contrapose! hx
  simp only [hx, not_false_eq_true, kl_of_not_ac]

@[simp]
lemma condKL_of_not_integrable (h : ¬ Integrable (fun x ↦ (kl (κ x) (η x)).toReal) μ) :
    condKL κ η μ = ⊤ := if_neg (not_and_of_not_right _ h)

@[simp]
lemma condKL_of_not_integrable' (h : ¬ Integrable (fun a ↦ integral (κ a) (llr (κ a) (η a))) μ) :
    condKL κ η μ = ⊤ := by
  contrapose! h
  have hh : (fun a => integral (κ a) (llr (κ a) (η a))) =ᵐ[μ] fun a => (kl (κ a) (η a)).toReal := by
    have h1 := of_not_not (condKL_of_not_ae_ac.mt h)
    have h2 := of_not_not (condKL_of_not_ae_finite.mt h)
    filter_upwards [h1, h2] with x hx1 hx2
    rw [kl_of_ac_of_integrable hx1 (of_not_not (kl_of_not_integrable.mt hx2))]
    simp only [EReal.toReal_coe]
  refine Integrable.congr ?_ hh.symm
  exact of_not_not (condKL_of_not_integrable.mt h)

lemma condKL_eq_condFDiv [IsFiniteKernel κ] [IsFiniteKernel η] :
    condKL κ η μ = condFDiv (fun x ↦ x * log x) κ η μ := by
  by_cases h1 : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤
  swap;
  · simp [h1]
    refine (condFDiv_of_not_ae_finite ?_).symm
    convert h1 using 4 with x
    rw [kl_eq_fDiv]
  by_cases h2 : Integrable (fun x ↦ (kl (κ x) (η x)).toReal) μ
  swap;
  · simp [h2]
    refine (condFDiv_of_not_integrable ?_).symm
    convert h2 using 4 with x
    rw [← kl_eq_fDiv]
  simp only [ne_eq, h1, h2, condKL_of_ae_finite_of_integrable, ← kl_eq_fDiv, condFDiv_eq']

@[simp]
lemma condKL_self (κ : kernel α β) (μ : Measure α) [IsFiniteKernel κ] : condKL κ κ μ = 0 := by
  simp only [kl_self, ne_eq, not_false_eq_true, eventually_true, EReal.toReal_zero, integrable_zero,
    condKL_of_ae_finite_of_integrable, integral_zero, EReal.coe_zero, EReal.zero_ne_top]

lemma condKL_ne_bot (κ η : kernel α β) (μ : Measure α) : condKL κ η μ ≠ ⊥ := by
  rw [condKL]
  split_ifs with h
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
  · norm_num

lemma condKL_nonneg (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] (μ : Measure α) :
    0 ≤ condKL κ η μ := by
  rw [condKL_eq_condFDiv]
  apply condFDiv_nonneg
  · exact Real.convexOn_mul_log
  · exact Real.continuous_mul_log.continuousOn
  · norm_num

-- TODO : regarding the next 2 lemmas, should we keep them as they are (derived from the fDiv), or should we prove them using the kl_compProd? it's probabily better to leave them like this, since kl_compProd has slightly stronger hypothesis. Though maybe we can relax some of these hypothesis.
lemma kl_compProd_left [CountablyGenerated β] (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsFiniteKernel η] :
    kl (μ ⊗ₘ κ) (μ ⊗ₘ η) = condKL κ η μ := by
  rw [kl_eq_fDiv, condKL_eq_condFDiv]
  exact fDiv_compProd_left μ κ η (by measurability) Real.convexOn_mul_log

lemma kl_compProd_right [CountablyGenerated β] (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ : kernel α β) [IsMarkovKernel κ] :
    kl (μ ⊗ₘ κ) (ν ⊗ₘ κ) = kl μ ν := by
  rw [kl_eq_fDiv, kl_eq_fDiv]
  exact fDiv_compProd_right μ ν κ (by measurability) Real.convexOn_mul_log


-- TODO : we are doing all the theory using natural log and eponential, is there any point in refactoring all to include the general case with arbitrary base?

#check kernel.Measure.absolutelyContinuous_compProd_iff.mpr.mt

#check Set.setOf_subset_setOf

-- TODO : this two lemmas should be moved to the right place
lemma ae_int_mul_rnDeriv_of_ae_int [SigmaFinite μ] [SigmaFinite ν] (g : α → β → ℝ)
    (h : ∀ᵐ a ∂μ, Integrable (fun x => g a x) (κ a)) :
    ∀ᵐ a ∂ν, Integrable (fun x ↦ (μ.rnDeriv ν a).toReal * g a x) (κ a) := by
  apply @Measure.ae_rnDeriv_ne_zero_imp_of_ae _ _ _ ν at h
  filter_upwards [h] with a ha
  by_cases h_zero : μ.rnDeriv ν a = 0
  · rw [h_zero]
    simp only [ENNReal.zero_toReal, zero_mul, integrable_zero]
  · apply Integrable.const_mul
    exact ha h_zero

lemma ae_int_of_ae_int_mul_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (g : α → β → ℝ)
    (h : ∀ᵐ a ∂ν, Integrable (fun x ↦ (μ.rnDeriv ν a).toReal * g a x) (κ a)) :
    ∀ᵐ a ∂μ, Integrable (fun x => g a x) (κ a) := by
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_toReal_ne_zero hμν] with a ha h_zero
  apply (integrable_const_mul_iff _ (fun x ↦ g a x)).mp
  · exact ha
  · simp only [isUnit_iff_ne_zero, ne_eq, h_zero, not_false_eq_true]

lemma integrable_llr_compProd_of_integrable_llr [CountablyGenerated β] [IsMarkovKernel κ]
    [IsFiniteKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_prod : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (hμν : Integrable (llr μ ν) μ) (hκη_int : Integrable (fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)) μ)
    (hκη_ae : ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) :
    Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) := by
  rw [← integrable_rnDeriv_mul_log_iff h_prod]
  rw [integrable_f_rnDeriv_compProd_iff (by measurability) Real.convexOn_mul_log]
  simp_rw [ENNReal.toReal_mul]
  have ⟨hμν_ac, hκη_ac⟩ := kernel.Measure.absolutelyContinuous_compProd_iff.mp h_prod
  have hκη_top : ∀ᵐ (x : α) ∂μ, kl (κ x) (η x) ≠ ⊤ := by
    filter_upwards [hκη_ac, hκη_ae] with x hx hx2
    apply kl_eq_top_iff.mp.mt
    push_neg
    exact ⟨hx, hx2⟩
  have hμν_zero := Measure.rnDeriv_toReal_ne_zero hμν_ac
  constructor
  · simp_rw [mul_assoc]
    apply ae_int_mul_rnDeriv_of_ae_int
    filter_upwards [hκη_ac, hκη_top, hμν_zero] with a ha h_top hμν_zero
    apply (MeasureTheory.integrable_rnDeriv_smul_iff ha).mpr
    apply Integrable.congr _ _
    · exact fun x ↦ log ((∂μ/∂ν) a).toReal + log ((∂κ a/∂η a) x).toReal
    swap
    · have hκη_zero := Measure.rnDeriv_toReal_ne_zero ha
      filter_upwards [hκη_zero] with a hκη_zero
      rw [Real.log_mul hμν_zero hκη_zero]
    apply Integrable.add (integrable_const _)
    apply Integrable.congr (of_not_not (kl_of_not_integrable.mt h_top))
    rw [llr_def]
  · simp_rw [mul_assoc, integral_mul_left]
    apply (MeasureTheory.integrable_rnDeriv_smul_iff hμν_ac).mpr
    have h : (fun a ↦ log ((∂μ/∂ν) a).toReal + ∫ x, log ((∂κ a/∂η a) x).toReal ∂κ a)
        =ᵐ[μ] (fun a ↦ ∫ x, ((∂κ a/∂η a) x).toReal
        * log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) x).toReal) ∂η a) := by
      filter_upwards [hκη_ac, hμν_zero, hκη_top] with a ha hμν_zero hκη_top
      calc
        _ = ∫ (x : β), log ((∂μ/∂ν) a).toReal + log ((∂κ a/∂η a) x).toReal ∂κ a := by
          rw [integral_add (integrable_const _)]
          · simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
          · rw [← llr_def]
            exact of_not_not (kl_of_not_integrable.mt hκη_top)
        _ = ∫ x, log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) x).toReal) ∂κ a := by
          have hκη_zero := Measure.rnDeriv_toReal_ne_zero ha
          apply integral_congr_ae
          filter_upwards [hκη_zero] with x hκη_zero
          rw [Real.log_mul hμν_zero hκη_zero]
        _ = _ := (integral_rnDeriv_smul ha).symm
    apply Integrable.congr _ h
    apply Integrable.add
    · rw [← llr_def]
      exact hμν
    · simp_rw [← llr_def]
      exact hκη_int

lemma ae_integrable_llr_of_integrable_llr_compProd [CountablyGenerated β] [IsMarkovKernel κ] -- this is external lemma 3
    [IsFiniteKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_prod : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a) := by
  have ⟨hμν_ac, hκη_ac⟩ := kernel.Measure.absolutelyContinuous_compProd_iff.mp h_prod
  have hμν_zero := Measure.rnDeriv_toReal_ne_zero hμν_ac --verify that these have are actually used
  -- consider if we also need the have h like in the following proof
  rw [← integrable_rnDeriv_mul_log_iff h_prod] at h_int
  rw [integrable_f_rnDeriv_compProd_iff (by measurability) Real.convexOn_mul_log] at h_int
  replace h_int := h_int.1
  simp_rw [ENNReal.toReal_mul, mul_assoc] at h_int
  apply ae_int_of_ae_int_mul_rnDeriv hμν_ac at h_int
  filter_upwards [h_int, hκη_ac, hμν_zero] with a h_int hκη_ac hμν_zero
  have h : (fun x ↦ log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) x).toReal))
      =ᵐ[κ a] (fun x ↦ log (((∂μ/∂ν) a).toReal) + log (((∂κ a/∂η a) x).toReal)) := by
    have hκη_zero := Measure.rnDeriv_toReal_ne_zero hκη_ac
    filter_upwards [hκη_zero] with x hκη_zero
    rw [Real.log_mul hμν_zero hκη_zero]
  apply (MeasureTheory.integrable_rnDeriv_smul_iff hκη_ac).mp at h_int
  replace h_int := Integrable.congr h_int h
  -- rw [← llr, ← llr] at h_int
  --same problem that we have in the following lemma where we need to split a hypothesis of Integrable (a + b) into Integrable a and Integrable b, maybe here it is easier, since one of the terms is constant. I didn't find the lemma, it may be worth adding it to mathlib, the fact that if the measure is finite then f is integrable iff f + c is integrable, for a constant c.
  sorry
  --rw [← llr_def] at h_int -- once we solve the previous problem, this should close the goal


lemma integrable_llr_of_integrable_llr_compProd [CountablyGenerated β] [IsMarkovKernel κ] -- this is external lemma 1
    [IsFiniteKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_prod : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    Integrable (llr μ ν) μ := by
  have ⟨hμν_ac, hκη_ac⟩ := kernel.Measure.absolutelyContinuous_compProd_iff.mp h_prod
  have hμν_zero := Measure.rnDeriv_toReal_ne_zero hμν_ac
  have h : (fun a ↦ log ((∂μ/∂ν) a).toReal + ∫ x, log ((∂κ a/∂η a) x).toReal ∂κ a)
      =ᵐ[μ] (fun a ↦ ∫ x, ((∂κ a/∂η a) x).toReal
      * log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) x).toReal) ∂η a) := by
    filter_upwards [hκη_ac, hμν_zero, ae_integrable_llr_of_integrable_llr_compProd h_prod h_int]
      with a ha hμν_zero hκη_int
    calc
      _ = ∫ (x : β), log ((∂μ/∂ν) a).toReal + log ((∂κ a/∂η a) x).toReal ∂κ a := by
        rw [llr_def] at hκη_int
        rw [integral_add (integrable_const _) hκη_int]
        simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
      _ = ∫ x, log (((∂μ/∂ν) a).toReal * ((∂κ a/∂η a) x).toReal) ∂κ a := by
        have hκη_zero := Measure.rnDeriv_toReal_ne_zero ha
        apply integral_congr_ae
        filter_upwards [hκη_zero] with x hκη_zero
        rw [Real.log_mul hμν_zero hκη_zero]
      _ = _ := (integral_rnDeriv_smul ha).symm
  rw [← integrable_rnDeriv_mul_log_iff h_prod] at h_int
  rw [integrable_f_rnDeriv_compProd_iff (by measurability) Real.convexOn_mul_log] at h_int
  replace h_int := h_int.2
  simp_rw [ENNReal.toReal_mul] at h_int
  -- have hκη_top : ∀ᵐ (x : α) ∂μ, kl (κ x) (η x) ≠ ⊤ := by --TODO : check that these have are actually used
  --   filter_upwards [hκη_ac, hκη_ae] with x hx hx2
  --   apply kl_eq_top_iff.mp.mt
  --   push_neg
  --   exact ⟨hx, hx2⟩
  simp_rw [mul_assoc, integral_mul_left] at h_int
  apply (MeasureTheory.integrable_rnDeriv_smul_iff hμν_ac).mp at h_int
  replace h_int := Integrable.congr h_int h.symm

  -- here we have to say that if the sum is integrable then the two terms are integrable, this is not true in general, but in this case it is, since the two terms are nonnegative, I didn't find a lemma for this, I wonder if there is something useful in mathlib, or if I have to prove it myself. Probably to prove it we must also assume some measurability conditions on the two functions, I hope they are easy to prove in this case.
  sorry
  --rw [← llr_def] at h_int -- once we solve the previous problem, this should close the goal

lemma integrable_integral_llr_of_integrable_llr_compProd [CountablyGenerated β] [IsMarkovKernel κ] -- this is external lemma 2
    [IsFiniteKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_prod : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    Integrable (fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)) μ := by
  sorry




#check Measure.rnDeriv_toReal_ne_zero
#check kernel.rnDeriv_toReal_ne_zero
#check integrable_rnDeriv_smul_iff
#check Integrable.const_mul
#check kernel.rnDeriv_eq_rnDeriv_measure
#check integral_smul_const
#check integral_smul
#check integral_rnDeriv_smul
#check Integrable.congr
--TODO : decide what to do with the next lemma. Maybe incorporate it in the main proof, or maybe rename it and put in the right place, another option is also to 'cut' the the proof a bit earlier, incorporate the last part in the main proof and leave the first part as a separate lemma, putting it in the right place and renaming it accordingly.
-- I think a good way to split this lemma is the following one, because itcuts the proof in a way s.t. both the hypothesis and the conclusions are sated in terms of the llr

lemma kl_eq_top_or_condKL_eq_top_of_integrable_llr_compProd [CountablyGenerated β] [IsMarkovKernel κ] [IsFiniteKernel η]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_prod : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h : ¬ Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ) : (kl μ ν = ⊤) ∨ (condKL κ η μ = ⊤) := by
  contrapose! h
  apply integrable_llr_compProd_of_integrable_llr h_prod <;>
  contrapose! h <;> aesop

#check integrable_f_rnDeriv_mul_kernel -- this cannot be used, because it assumes that η is markov, but we don't have that hypothesis
lemma kl_compProdAux1 [CountablyGenerated β] [IsMarkovKernel κ] [IsFiniteKernel η]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_prod : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ) : Integrable (llr μ ν) μ := by
    rw [← integrable_rnDeriv_mul_log_iff h_prod] at h
    sorry


-- TODO : consider changing the arguments, in particular the kernels and measures may be put between curly braces, but maybe not, since there are no other hypothesis that mention them, so they cannot be inferred
lemma kl_compProd [CountablyGenerated β] (κ η : kernel α β) [IsMarkovKernel κ] [IsFiniteKernel η]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl (μ ⊗ₘ κ) (ν ⊗ₘ η) = kl μ ν + condKL κ η μ := by
  by_cases h_prod : (μ ⊗ₘ κ) ≪ (ν ⊗ₘ η)
  swap
  · simp only [h_prod, not_false_eq_true, kl_of_not_ac]
    have h := kernel.Measure.absolutelyContinuous_compProd_iff.mpr.mt h_prod
    set_option push_neg.use_distrib true in push_neg at h
    rcases h with (hμν | hκη)
    · simp only [hμν, not_false_eq_true, kl_of_not_ac]
      exact (EReal.top_add_of_ne_bot (condKL_ne_bot _ _ _)).symm
    · simp only [hκη, not_false_eq_true, condKL_of_not_ae_ac]
      exact (EReal.add_top_of_ne_bot (kl_ne_bot _ _)).symm
  have ⟨hμν, hκη⟩ := kernel.Measure.absolutelyContinuous_compProd_iff.mp h_prod
  by_cases h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)
  swap
  · simp only [h_int, not_false_eq_true, kl_of_not_integrable]
    apply kl_eq_top_or_condKL_eq_top_of_integrable_llr_compProd h_prod at h_int --here we use the auxiliary lemma
    set_option push_neg.use_distrib true in push_neg at h_int
    rcases h_int with (h | h) <;> rw [h]
    · exact (EReal.top_add_of_ne_bot (condKL_ne_bot _ _ _)).symm
    · exact (EReal.add_top_of_ne_bot (kl_ne_bot _ _)).symm
  have intμν := integrable_llr_of_integrable_llr_compProd h_prod h_int -- here we use the external lemma 1
  have intκη : Integrable (fun x ↦ ∫ (y : β), log (kernel.rnDeriv κ η x y).toReal ∂κ x) μ := by -- here we use the external lemma 2
    apply Integrable.congr (integrable_integral_llr_of_integrable_llr_compProd h_prod h_int)
    filter_upwards [hκη] with x hx
    apply integral_congr_ae
    filter_upwards [hx.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η x)] with y hy
    rw [hy, llr_def]
  have intκη2 := ae_integrable_llr_of_integrable_llr_compProd h_prod h_int -- here we use the external lemma 3
  calc kl (μ ⊗ₘ κ) (ν ⊗ₘ η) = ↑(∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂(μ ⊗ₘ κ)) :=
    kl_of_ac_of_integrable h_prod h_int
  _ = ↑(∫ (x : α), ∫ (y : β), llr (μ ⊗ₘ κ) (ν ⊗ₘ η) (x, y) ∂κ x ∂μ) := by
    norm_cast
    refine Measure.integral_compProd h_int
  _ = ↑(∫ (x : α), ∫ (y : β), log ((∂μ/∂ν) x * kernel.rnDeriv κ η x y).toReal ∂κ x ∂μ) := by
    norm_cast
    have h := hμν.ae_le (Measure.ae_ae_of_ae_compProd (kernel.rnDeriv_measure_compProd μ ν κ η))
    apply integral_congr_ae
    filter_upwards [h, hκη] with x hx hκηx
    apply integral_congr_ae
    filter_upwards [hκηx.ae_le hx] with y hy
    unfold llr
    congr
  _ = ↑(∫ (x : α), ∫ (y : β), log (μ.rnDeriv ν x).toReal
      + log (kernel.rnDeriv κ η x y).toReal ∂κ x ∂μ) := by
    norm_cast
    apply integral_congr_ae
    filter_upwards [hκη, Measure.rnDeriv_toReal_ne_zero hμν] with x hκηx hμν_pos
    apply integral_congr_ae
    filter_upwards [kernel.rnDeriv_toReal_ne_zero hκηx] with y hy
    simp only [ENNReal.toReal_mul]
    apply Real.log_mul hμν_pos hy
  _ = ↑(∫ (x : α), ∫ (_ : β), log (μ.rnDeriv ν x).toReal ∂κ x ∂μ)
      + ↑(∫ (x : α), ∫ (y : β), log (kernel.rnDeriv κ η x y).toReal ∂κ x ∂μ) := by
    norm_cast
    rw [← integral_add']
    simp only [Pi.add_apply]
    rotate_left
    · simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul, ← llr_def]
      exact intμν
    · exact intκη
    apply integral_congr_ae
    filter_upwards [hκη, intκη2] with x hx hκηx
    have h := hx.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η x)
    rw [← integral_add']
    rotate_left
    · simp only [integrable_const]
    · apply Integrable.congr hκηx
      filter_upwards [h] with y hy
      rw [hy, llr_def]
    apply integral_congr_ae
    filter_upwards
    intro a
    congr
  _ = ↑(∫ (x : α), log (μ.rnDeriv ν x).toReal ∂μ)
      + ↑(∫ (x : α), ∫ (y : β), log (kernel.rnDeriv κ η x y).toReal ∂κ x ∂μ) := by
    simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  _ = ↑(∫ (x : α), log (μ.rnDeriv ν x).toReal ∂μ)
      + ↑(∫ (x : α), ∫ (y : β), log ((κ x).rnDeriv (η x) y).toReal ∂κ x ∂μ) := by
    congr 2
    apply integral_congr_ae
    filter_upwards [hκη] with x hx
    have h := hx.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η x)
    apply integral_congr_ae
    filter_upwards [h] with y hy
    congr
  _ = kl μ ν + condKL κ η μ := by
    congr
    · rw [← llr_def, ← kl_of_ac_of_integrable hμν]
      exact intμν
    · simp_rw [← llr_def]
      rw [condKL_of_ae_finite_of_integrable _ _]
      rotate_left
      · filter_upwards [hκη, intκη2] with x hx hκηx
        intro h
        apply kl_eq_top_iff.mp at h
        tauto
      · apply Integrable.congr intκη
        filter_upwards [hκη, intκη2] with x hx hκηx
        rw [kl_of_ac_of_integrable hx hκηx, EReal.toReal_coe]
        apply integral_congr_ae
        filter_upwards [hx.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η x)] with y hy
        rw [hy, llr_def]
      norm_cast
      apply integral_congr_ae
      filter_upwards [hκη] with x hx
      by_cases h : Integrable (llr (κ x) (η x)) (κ x)
      · suffices hh : kl (κ x) (η x) = ∫ y, llr (κ x) (η x) y ∂(κ x) from by simp [hh]
        exact kl_of_ac_of_integrable (hx) h
      · rw [kl_of_not_integrable h]
        simp only [h, not_false_eq_true, integral_undef, EReal.toReal_top]



end Conditional

end ProbabilityTheory

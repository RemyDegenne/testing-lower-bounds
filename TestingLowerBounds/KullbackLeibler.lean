/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- theorem foo (n : Nat) : 0 ≤ n := by exact? -- trick to make exact? work TODO : erase this when we are done

import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import TestingLowerBounds.FDiv.CondFDiv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TestingLowerBounds.ForMathlib.L1Space
import TestingLowerBounds.ForMathlib.LogLikelihoodRatioCompProd


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

-- TODO : add the equivalent of integrable_fDiv_iff for kl

section kl_nonneg

@[simp]
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
    ∧ (Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ)
  then ((μ[fun a ↦ (kl (κ a) (η a)).toReal] : ℝ) : EReal)
  else ⊤

lemma condKL_of_ae_finite_of_integrable (h1 : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤)
    (h2 : Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = (μ[fun a ↦ (kl (κ a) (η a)).toReal] : ℝ) := if_pos ⟨h1, h2⟩

@[simp]
lemma condKL_of_not_ae_finite (h : ¬ (∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤)) :
    condKL κ η μ = ⊤ := if_neg (not_and_of_not_left _ h)

@[simp]
lemma condKL_of_not_ae_integrable (h : ¬ ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) :
    condKL κ η μ = ⊤ := by
  apply condKL_of_not_ae_finite
  contrapose! h
  filter_upwards [h] with a ha
  contrapose! ha
  simp only [ha, ne_eq, not_false_eq_true, kl_of_not_integrable]

@[simp]
lemma condKL_of_not_ae_ac (h : ¬ ∀ᵐ x ∂μ, κ x ≪ η x) :
    condKL κ η μ = ⊤ := by
  apply condKL_of_not_ae_finite
  contrapose! h
  filter_upwards [h] with x ha
  contrapose! ha
  simp only [ha, not_false_eq_true, kl_of_not_ac]

@[simp]
lemma condKL_of_not_integrable (h : ¬ Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = ⊤ := if_neg (not_and_of_not_right _ h)

@[simp]
lemma condKL_of_not_integrable' (h : ¬ Integrable (fun a ↦ integral (κ a) (llr (κ a) (η a))) μ) :
    condKL κ η μ = ⊤ := by
  contrapose! h
  have hh : (fun a => integral (κ a) (llr (κ a) (η a))) =ᵐ[μ] fun a => (kl (κ a) (η a)).toReal := by
    have h1 := of_not_not (condKL_of_not_ae_ac.mt h)
    have h2 := of_not_not (condKL_of_not_ae_finite.mt h)
    filter_upwards [h1, h2] with a ha1 ha2
    rw [kl_of_ac_of_integrable ha1 (of_not_not (kl_of_not_integrable.mt ha2))]
    simp only [EReal.toReal_coe]
  exact Integrable.congr (of_not_not (condKL_of_not_integrable.mt h)) hh.symm

lemma condKL_eq_condFDiv [IsFiniteKernel κ] [IsFiniteKernel η] :
    condKL κ η μ = condFDiv (fun x ↦ x * log x) κ η μ := by
  by_cases h1 : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤
  swap
  · simp [h1]
    refine (condFDiv_of_not_ae_finite ?_).symm
    convert h1 using 4 with a
    rw [kl_eq_fDiv]
  by_cases h2 : Integrable (fun x ↦ (kl (κ x) (η x)).toReal) μ
  swap
  · simp [h2]
    refine (condFDiv_of_not_integrable ?_).symm
    convert h2 using 4 with a
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


-- TODO : consider changing the arguments, in particular the kernels and measures may be put between curly braces, but maybe not, since there are no other hypothesis that mention them, so they cannot be inferred.
-- TODO : the name of this lemma in the blueprint is kl_chain_rule, is it ok to keep it like this in lean or should we change one of the two names?

/--The chain rule for the KL divergence.-/
lemma kl_compProd [CountablyGenerated β] (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
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
    rw [integrable_llr_compProd_iff h_prod] at h_int
    set_option push_neg.use_distrib true in push_neg at h_int
    rcases h_int with ((h | h) | h) <;> simp [h, EReal.top_add_of_ne_bot, condKL_ne_bot, EReal.add_top_of_ne_bot, kl_ne_bot]
  have intμν := integrable_llr_of_integrable_llr_compProd h_prod h_int
  have intκη : Integrable (fun a ↦ ∫ (x : β), log (kernel.rnDeriv κ η a x).toReal ∂κ a) μ := by
    apply Integrable.congr (integrable_integral_llr_of_integrable_llr_compProd h_prod h_int)
    filter_upwards [hκη] with a ha
    apply integral_congr_ae
    filter_upwards [ha.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η a)] with x hx
    rw [hx, llr_def]
  have intκη2 := ae_integrable_llr_of_integrable_llr_compProd h_prod h_int
  calc kl (μ ⊗ₘ κ) (ν ⊗ₘ η) = ↑(∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂(μ ⊗ₘ κ)) :=
    kl_of_ac_of_integrable h_prod h_int
  _ = ↑(∫ (a : α), ∫ (x : β), llr (μ ⊗ₘ κ) (ν ⊗ₘ η) (a, x) ∂κ a ∂μ) := by
    norm_cast
    exact Measure.integral_compProd h_int
  _ = ↑(∫ (a : α), ∫ (x : β), log ((∂μ/∂ν) a * kernel.rnDeriv κ η a x).toReal ∂κ a ∂μ) := by
    norm_cast
    have h := hμν.ae_le (Measure.ae_ae_of_ae_compProd (kernel.rnDeriv_measure_compProd μ ν κ η))
    apply integral_congr_ae
    filter_upwards [h, hκη] with a ha hκηa
    apply integral_congr_ae
    filter_upwards [hκηa.ae_le ha] with x hx
    unfold llr
    congr
  _ = ↑(∫ (a : α), ∫ (x : β), log (μ.rnDeriv ν a).toReal
      + log (kernel.rnDeriv κ η a x).toReal ∂κ a ∂μ) := by
    norm_cast
    apply integral_congr_ae
    filter_upwards [hκη, Measure.rnDeriv_toReal_pos hμν] with a hκηa hμν_pos
    have hμν_zero : (μ.rnDeriv ν a).toReal ≠ 0 := by linarith
    apply integral_congr_ae
    filter_upwards [kernel.rnDeriv_toReal_pos hκηa] with x hx
    have hκη_zero : (kernel.rnDeriv κ η a x).toReal ≠ 0 := by linarith
    simp only [ENNReal.toReal_mul]
    apply Real.log_mul hμν_zero hκη_zero
  _ = ↑(∫ (a : α), ∫ (_ : β), log (μ.rnDeriv ν a).toReal ∂κ a ∂μ)
      + ↑(∫ (a : α), ∫ (x : β), log (kernel.rnDeriv κ η a x).toReal ∂κ a ∂μ) := by
    norm_cast
    rw [← integral_add']
    simp only [Pi.add_apply]
    rotate_left
    · simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul, ← llr_def]
      exact intμν
    · exact intκη
    apply integral_congr_ae
    filter_upwards [hκη, intκη2] with a ha hκηa
    have h := ha.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η a)
    rw [← integral_add']
    rotate_left
    · simp only [integrable_const]
    · apply Integrable.congr hκηa
      filter_upwards [h] with x hx
      rw [hx, llr_def]
    apply integral_congr_ae
    filter_upwards
    intro a
    congr
  _ = ↑(∫ (a : α), log (μ.rnDeriv ν a).toReal ∂μ)
      + ↑(∫ (a : α), ∫ (x : β), log (kernel.rnDeriv κ η a x).toReal ∂κ a ∂μ) := by
    simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  _ = ↑(∫ (a : α), log (μ.rnDeriv ν a).toReal ∂μ)
      + ↑(∫ (a : α), ∫ (x : β), log ((κ a).rnDeriv (η a) x).toReal ∂κ a ∂μ) := by
    congr 2
    apply integral_congr_ae
    filter_upwards [hκη] with a ha
    have h := ha.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η a)
    apply integral_congr_ae
    filter_upwards [h] with x hx
    congr
  _ = kl μ ν + condKL κ η μ := by
    congr
    · rw [← llr_def, ← kl_of_ac_of_integrable hμν]
      exact intμν
    · simp_rw [← llr_def]
      rw [condKL_of_ae_finite_of_integrable _ _]
      rotate_left
      · filter_upwards [hκη, intκη2] with a ha hκηa
        intro h
        apply kl_eq_top_iff.mp at h
        tauto
      · apply Integrable.congr intκη
        filter_upwards [hκη, intκη2] with a ha hκηa
        rw [kl_of_ac_of_integrable ha hκηa, EReal.toReal_coe]
        apply integral_congr_ae
        filter_upwards [ha.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η a)] with x hx
        rw [hx, llr_def]
      norm_cast
      apply integral_congr_ae
      filter_upwards [hκη] with a ha
      by_cases h : Integrable (llr (κ a) (η a)) (κ a)
      · suffices hh : kl (κ a) (η a) = ∫ x, llr (κ a) (η a) x ∂(κ a) from by simp [hh]
        exact kl_of_ac_of_integrable (ha) h
      · rw [kl_of_not_integrable h]
        simp only [h, not_false_eq_true, integral_undef, EReal.toReal_top]

end Conditional

end ProbabilityTheory
-- TODO : update the blueprint and put the lemmas in the relevant files, if necessary create some files and put them in the ForMathlib folder, after having done this change branch so that this one is dedicated to the PR
-- TODO : add the chain rule, product version, then the tensorization for kl (see the one for the Renyi divergence)

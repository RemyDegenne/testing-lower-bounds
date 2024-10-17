/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.ForMathlib.LogLikelihoodRatioCompProd

/-!
# Kullback-Leibler divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology BigOperators

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

section Move

lemma llr_self (μ : Measure α) [SigmaFinite μ] : llr μ μ =ᵐ[μ] 0 := by
  unfold llr
  filter_upwards [μ.rnDeriv_self] with a ha
  simp [ha]

end Move

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

/-- If `μ ≪ ν`, then `toReal` of the Kullback-Leibler divergence is equal to an integral,
without any integrability condition. Not true in general without `μ ≪ ν`, as the integral might be
finite but non-zero. -/
lemma kl_toReal_of_ac (h : μ ≪ ν) : (kl μ ν).toReal = ∫ a, llr μ ν a ∂μ := by
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [kl_of_ac_of_integrable h h_int, EReal.toReal_coe]
  · rw [kl_of_not_integrable h_int, integral_undef h_int, EReal.toReal_top]

lemma rightDeriv_mul_log {x : ℝ} (hx : x ≠ 0) : rightDeriv (fun x ↦ x * log x) x = log x + 1 :=
  rightDeriv_of_hasDerivAt (Real.hasDerivAt_mul_log hx)

lemma derivAtTop_mul_log : derivAtTop (fun x ↦ x * log x) = ⊤ := by
  refine derivAtTop_of_tendsto_atTop ?_
  have h_tendsto : Tendsto (fun x ↦ log x + 1) atTop atTop :=
    tendsto_log_atTop.atTop_add tendsto_const_nhds
  refine (tendsto_congr' ?_).mpr h_tendsto
  rw [EventuallyEq, eventually_atTop]
  exact ⟨1, fun _ hx ↦ rightDeriv_mul_log (zero_lt_one.trans_le hx).ne'⟩

@[simp]
lemma kl_self (μ : Measure α) [SigmaFinite μ] : kl μ μ = 0 := by
  have h := llr_self μ
  rw [kl, if_pos]
  · simp [integral_congr_ae h]
  · rw [integrable_congr h]
    exact ⟨Measure.AbsolutelyContinuous.rfl, integrable_zero _ _ μ⟩

@[simp]
lemma kl_zero_left : kl 0 ν = 0 := by
  convert kl_of_ac_of_integrable (Measure.AbsolutelyContinuous.zero _) integrable_zero_measure
  simp only [integral_zero_measure, EReal.coe_zero]

@[simp]
lemma kl_zero_right [NeZero μ] : kl μ 0 = ⊤ :=
  kl_of_not_ac (Measure.absolutelyContinuous_zero_iff.mp.mt (NeZero.ne _))

lemma kl_eq_top_iff : kl μ ν = ⊤ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ := by
  constructor <;> intro h <;> push_neg at *
  · contrapose! h
    rw [kl_of_ac_of_integrable h.1 h.2]
    exact EReal.coe_ne_top _
  · rcases or_not_of_imp h with (h | h) <;> simp [h]

lemma kl_ne_top_iff : kl μ ν ≠ ⊤ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ := by
  rw [ne_eq, kl_eq_top_iff]
  push_neg
  rfl

lemma kl_ne_top_iff' : kl μ ν ≠ ⊤ ↔ kl μ ν = ∫ x, llr μ ν x ∂μ := by
  constructor
  · rw [kl_ne_top_iff]
    rintro ⟨h1, h2⟩
    rw [kl_of_ac_of_integrable h1 h2]
  · simp_all only [ne_eq, EReal.coe_ne_top, not_false_eq_true, implies_true]

@[simp]
lemma kl_ne_bot (μ ν : Measure α) : kl μ ν ≠ ⊥ := by
  rw [kl]
  split_ifs with h
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
  · norm_num

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

lemma measurable_kl {β : Type*} [MeasurableSpace β] [CountableOrCountablyGenerated α β]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦ kl (κ a) (η a)) := by
  simp_rw [kl_eq_fDiv]
  exact measurable_fDiv _ _ continuous_mul_log.stronglyMeasurable

section kl_nonneg

lemma kl_ge_mul_log' [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (μ .univ).toReal * log (μ .univ).toReal ≤ kl μ ν :=
  (le_fDiv_of_ac convexOn_mul_log continuous_mul_log.continuousOn hμν).trans_eq
    kl_eq_fDiv.symm

lemma kl_ge_mul_log (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ .univ).toReal * log ((μ .univ).toReal / (ν .univ).toReal) ≤ kl μ ν := by
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
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  let ν' := (ν .univ)⁻¹ • ν
  have : IsProbabilityMeasure ν' := by
    constructor
    simp only [ν', Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ENNReal.mul_inv_cancel]
    · simp [hν]
    · exact measure_ne_top _ _
  have hμν' : μ ≪ ν' := by
    refine Measure.AbsolutelyContinuous.trans hμν (Measure.absolutelyContinuous_smul ?_)
    simp [measure_ne_top ν]
  have h := kl_ge_mul_log' hμν'
  rw [kl_of_ac_of_integrable hμν', integral_congr_ae (llr_smul_right hμν (ν .univ)⁻¹ _ _)] at h
  rotate_left
  · simp [measure_ne_top ν _]
  · simp [hν]
  · rw [integrable_congr (llr_smul_right hμν (ν .univ)⁻¹ _ _)]
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

lemma kl_nonneg' (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ .univ ≥ ν .univ) :
    0 ≤ kl μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · rw [kl_of_not_ac hμν]; simp
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · rw [kl_of_not_integrable h_int]; simp
  calc 0
    ≤ ((μ .univ).toReal : EReal) * log ((μ .univ).toReal / (ν .univ).toReal) := by
        by_cases h_zero : NeZero ν
        swap; · simp [not_neZero.mp h_zero]
        refine mul_nonneg (EReal.coe_nonneg.mpr ENNReal.toReal_nonneg) ?_
        norm_cast
        refine log_nonneg ((one_le_div ?_).mpr ?_)
        · exact ENNReal.toReal_pos (NeZero.ne' _).symm (measure_ne_top _ _)
        · gcongr
          exact measure_ne_top _ _
  _ ≤ kl μ ν := kl_ge_mul_log _ _

/-- **Gibbs' inequality**: the Kullback-Leibler divergence between two probability distributions is
nonnegative. -/
lemma kl_nonneg (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ kl μ ν := kl_nonneg' μ ν (by simp)

/-- **Converse Gibbs' inequality**: the Kullback-Leibler divergence between two finite measures is
zero if and only if the two distributions are equal. -/
lemma kl_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_mass : μ .univ = ν .univ) :
    kl μ ν = 0 ↔ μ = ν :=
  kl_eq_fDiv (μ := μ) (ν := ν) ▸ fDiv_eq_zero_iff h_mass derivAtTop_mul_log
    Real.strictConvexOn_mul_log Real.continuous_mul_log.continuousOn (by norm_num)

/-- **Converse Gibbs' inequality**: the Kullback-Leibler divergence between two probability
distributions is zero if and only if the two distributions are equal. -/
lemma kl_eq_zero_iff' [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    kl μ ν = 0 ↔ μ = ν := kl_eq_zero_iff (by simp)

end kl_nonneg

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β}

lemma kl_comp_le_compProd [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    kl (κ ∘ₘ μ) (η ∘ₘ ν) ≤ kl (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simp_rw [kl_eq_fDiv]
  exact fDiv_comp_le_compProd μ ν κ η continuous_mul_log.stronglyMeasurable
    convexOn_mul_log continuous_mul_log.continuousOn

/--The **Data Processing Inequality** for the Kullback-Leibler divergence. -/
lemma kl_comp_right_le [Nonempty α] [StandardBorelSpace α] [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    kl (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ kl μ ν := by
  simp_rw [kl_eq_fDiv]
  exact fDiv_comp_right_le μ ν κ continuous_mul_log.stronglyMeasurable
    convexOn_mul_log continuous_mul_log.continuousOn

end DataProcessingInequality

end ProbabilityTheory

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
--import TestingLowerBounds.ForMathlib.LogLikelihoodRatioCompProd
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import TestingLowerBounds.FDiv.CompProd.CompProd
import TestingLowerBounds.FDiv.Measurable

/-!
# Kullback-Leibler divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open Real MeasureTheory Filter MeasurableSpace Set

open scoped ENNReal NNReal Topology BigOperators

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

section Move

lemma llr_self (μ : Measure α) [SigmaFinite μ] : llr μ μ =ᵐ[μ] 0 := by
  unfold llr
  filter_upwards [μ.rnDeriv_self] with a ha
  simp [ha]

end Move

section MulLog

@[simp]
lemma rightDeriv_mul_log {x : ℝ} (hx : x ≠ 0) : rightDeriv (fun x ↦ x * log x) x = log x + 1 :=
  rightDeriv_of_hasDerivAt (Real.hasDerivAt_mul_log hx)

lemma rightDeriv_mul_log_one : rightDeriv (fun x ↦ x * log x) 1 = 1 := by simp

lemma tendsto_mul_log_atTop : Tendsto (rightDeriv fun x ↦ x * log x) atTop atTop := by
  have h_tendsto : Tendsto (fun x ↦ log x + 1) atTop atTop :=
    tendsto_log_atTop.atTop_add tendsto_const_nhds
  refine (tendsto_congr' ?_).mpr h_tendsto
  rw [EventuallyEq, eventually_atTop]
  exact ⟨1, fun _ hx ↦ rightDeriv_mul_log (zero_lt_one.trans_le hx).ne'⟩

lemma integrable_rnDeriv_mul_log_iff [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    Integrable (fun a ↦ (μ.rnDeriv ν a).toReal * log (μ.rnDeriv ν a).toReal) ν
      ↔ Integrable (llr μ ν) μ :=
  integrable_rnDeriv_smul_iff hμν

lemma mul_log_add_one_sub_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x * log x + 1 - x := by
  refine ConvexOn.nonneg_of_todo (f := fun x ↦ x * log x + 1 - x) ?_ ?_ ?_ hx
  · have h := (convexOn_mul_log.subset (Ioi_subset_Ici le_rfl) (convex_Ioi _)).sub_one
    simp only [log_one, mul_zero, sub_zero, ne_eq, one_ne_zero, not_false_eq_true,
      rightDeriv_mul_log, zero_add, one_mul, sub_sub_eq_add_sub] at h
    exact h
  · simp
  · simp_rw [sub_eq_add_neg]
    rw [rightDeriv_add_apply', rightDeriv_add_const_apply]
    · sorry
    · sorry
    · sorry
    · sorry

lemma mul_log_add_one_sub_eq_zero_iff {x : ℝ} (hx : 0 ≤ x) : x * log x + 1 - x = 0 ↔ x = 1 := by
  sorry

end MulLog

section KLDivFun

noncomputable
def klDivFun : DivFunction := DivFunction.ofConvexOn (fun x ↦ x * log x)
  (convexOn_mul_log.subset (Set.Ioi_subset_Ici le_rfl) (convex_Ioi _))

@[simp] lemma klDivFun_apply_top : klDivFun ∞ = ∞ := by
  rw [klDivFun, DivFunction.ofConvexOn_apply_top]
  simp only [log_one, mul_zero, sub_zero, ne_eq, one_ne_zero, not_false_eq_true, rightDeriv_mul_log,
    zero_add, one_mul]
  sorry

lemma klDivFun_apply {x : ℝ≥0∞} (hx : x ≠ ∞) :
    klDivFun x = ENNReal.ofReal (x.toReal * log x.toReal + 1 - x.toReal) := by
  by_cases hx0 : x = 0
  · rw [klDivFun, hx0, DivFunction.ofConvexOn_apply_zero_of_continuousWithinAt]
    simp only [log_zero, mul_zero, log_one, sub_self, ne_eq, one_ne_zero, not_false_eq_true,
      rightDeriv_mul_log, zero_add, ENNReal.ofReal_one, ENNReal.zero_toReal, sub_zero]
    exact continuous_mul_log.continuousWithinAt
  · rw [klDivFun, DivFunction.ofConvexOn_apply _ hx0 hx]
    simp only [log_one, mul_zero, sub_zero, ne_eq, one_ne_zero, not_false_eq_true,
      rightDeriv_mul_log, zero_add, one_mul]
    rw [sub_sub_eq_add_sub]

@[simp]
lemma klDivFun_realFun_apply {x : ℝ} (hx : 0 ≤ x) : klDivFun.realFun x = x * log x + 1 - x := by
  rw [DivFunction.realFun, klDivFun_apply ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hx,
    ENNReal.toReal_ofReal]
  exact mul_log_add_one_sub_nonneg hx

@[simp] lemma derivAtTop_klDivFun : klDivFun.derivAtTop = ∞ :=
  DivFunction.derivAtTop_ofConvexOn_of_tendsto_atTop tendsto_mul_log_atTop

lemma eqOn_klDivFun_realFun : EqOn klDivFun.realFun (fun x ↦ x * log x + 1 - x) (Ioi 0) :=
  fun _ hx ↦ klDivFun_realFun_apply hx.le

lemma strictConvexOn_klDivFun :
    StrictConvexOn ℝ (Ioi 0) klDivFun.realFun := by
  refine StrictConvexOn.congr ?_ eqOn_klDivFun_realFun.symm
  simp_rw [add_sub_assoc]
  have h : StrictConvexOn ℝ (Ioi 0) fun x ↦ x * log x :=
    Real.strictConvexOn_mul_log.subset (Ioi_subset_Ici le_rfl) (convex_Ioi _)
  refine h.add_convexOn ?_
  exact (convexOn_const _ (convex_Ioi _)).sub (concaveOn_id (convex_Ioi _))

lemma lintegral_klDivFun_rnDeriv [SigmaFinite μ] [SigmaFinite ν] :
    ∫⁻ x, klDivFun (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x, ENNReal.ofReal ((μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal
        + 1 - (μ.rnDeriv ν x).toReal) ∂ν := by
  have h_ne_top := μ.rnDeriv_ne_top ν
  refine lintegral_congr_ae ?_
  filter_upwards [h_ne_top] with x hx
  rw [klDivFun_apply hx]

lemma todo_integral [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ∫ x, ((∂μ/∂ν) x).toReal * log ((∂μ/∂ν) x).toReal + 1 - ((∂μ/∂ν) x).toReal ∂ν
      = ∫ x, llr μ ν x ∂μ + (ν .univ).toReal - (μ .univ).toReal := by
  rw [integral_sub, integral_add, integral_const, Measure.integral_toReal_rnDeriv hμν, smul_eq_mul,
    mul_one]
  rotate_left
  · rwa [integrable_rnDeriv_mul_log_iff hμν]
  · exact integrable_const _
  · refine Integrable.add ?_ (integrable_const _)
    rwa [integrable_rnDeriv_mul_log_iff hμν]
  · exact Measure.integrable_toReal_rnDeriv
  congr 2
  exact integral_rnDeriv_smul hμν

lemma integral_llr_add_sub_measure_univ_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    0 ≤ ∫ x, llr μ ν x ∂μ + (ν .univ).toReal - (μ .univ).toReal := by
  rw [← todo_integral hμν h_int]
  refine integral_nonneg fun x ↦ ?_
  exact mul_log_add_one_sub_nonneg ENNReal.toReal_nonneg

lemma integral_llr_add_mul_log_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    0 ≤ ∫ x, llr μ ν x ∂μ + (μ univ).toReal * log (ν univ).toReal + 1 - (μ .univ).toReal := by
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  have : NeZero ν := ⟨hν⟩
  let ν' := (ν .univ)⁻¹ • ν
  have hμν' : μ ≪ ν' :=
    Measure.AbsolutelyContinuous.trans hμν (Measure.absolutelyContinuous_smul (by simp))
  have h := integral_llr_add_sub_measure_univ_nonneg hμν' ?_
  swap
  · rw [integrable_congr (llr_smul_right hμν (ν .univ)⁻¹ (by simp) (by simp [hν]))]
    exact h_int.sub (integrable_const _)
  rw [integral_congr_ae (llr_smul_right hμν (ν .univ)⁻¹ (by simp) (by simp [hν]))] at h
  rw [integral_sub h_int (integrable_const _), integral_const, smul_eq_mul] at h
  simp only [ENNReal.toReal_inv, log_inv, mul_neg, sub_neg_eq_add, measure_univ, ENNReal.one_toReal]
    at h
  exact h

lemma lintegral_klDivFun_of_not_integrable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : ¬ Integrable (llr μ ν) μ) :
    ∫⁻ x, klDivFun (μ.rnDeriv ν x) ∂ν = ∞ := by
  rw [lintegral_klDivFun_rnDeriv]
  have h : ¬ Integrable
      (fun x ↦ ((∂μ/∂ν) x).toReal * log ((∂μ/∂ν) x).toReal + 1 - ((∂μ/∂ν) x).toReal) ν := by
    refine fun h_int' ↦ h_int ?_
    simp_rw [add_sub_assoc] at h_int'
    rwa [integrable_add_iff_integrable_left', integrable_rnDeriv_mul_log_iff hμν] at h_int'
    exact (integrable_const _).sub Measure.integrable_toReal_rnDeriv
  have h_eq : (fun x ↦ ((∂μ/∂ν) x).toReal * log ((∂μ/∂ν) x).toReal + 1 - ((∂μ/∂ν) x).toReal)
      = fun x ↦ (ENNReal.ofReal
        (((∂μ/∂ν) x).toReal * log ((∂μ/∂ν) x).toReal + 1 - ((∂μ/∂ν) x).toReal)).toReal := by
    ext x
    rw [ENNReal.toReal_ofReal]
    exact mul_log_add_one_sub_nonneg ENNReal.toReal_nonneg
  simp_rw [h_eq] at h
  rw [integrable_toReal_iff] at h
  · exact not_not.mp h
  · refine (Measurable.ennreal_ofReal ?_).aemeasurable
    refine Measurable.sub (Measurable.add ?_ measurable_const)
      (μ.measurable_rnDeriv ν).ennreal_toReal
    exact continuous_mul_log.measurable.comp (μ.measurable_rnDeriv ν).ennreal_toReal
  · exact ae_of_all _ fun x ↦ ENNReal.ofReal_ne_top

lemma lintegral_klDivFun_eq_integral [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    ∫⁻ x, klDivFun (μ.rnDeriv ν x) ∂ν
      = ENNReal.ofReal (∫ x, llr μ ν x ∂μ + (ν .univ).toReal - (μ .univ).toReal) := by
  rw [lintegral_klDivFun_rnDeriv, ← ofReal_integral_eq_lintegral_ofReal]
  rotate_left
  · refine Integrable.sub ?_ Measure.integrable_toReal_rnDeriv
    refine Integrable.add ?_ (integrable_const _)
    rwa [integrable_rnDeriv_mul_log_iff hμν]
  · refine ae_of_all _ fun x ↦ ?_
    exact mul_log_add_one_sub_nonneg ENNReal.toReal_nonneg
  rw [todo_integral hμν h_int]

lemma lintegral_klDivFun_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    ∫⁻ x, klDivFun (μ.rnDeriv ν x) ∂ν = ∞ ↔ ¬ Integrable (llr μ ν) μ := by
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [lintegral_klDivFun_eq_integral hμν h_int]
    simp [h_int]
  · rw [lintegral_klDivFun_of_not_integrable hμν h_int]
    simp [h_int]

lemma lintegral_klDivFun_ne_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    ∫⁻ x, klDivFun (μ.rnDeriv ν x) ∂ν ≠ ∞ ↔ Integrable (llr μ ν) μ := by
  convert not_iff_not.mpr (lintegral_klDivFun_eq_top_iff hμν)
  rw [not_not]

end KLDivFun

open Classical in
/-- Kullback-Leibler divergence between two measures. -/
noncomputable def kl (μ ν : Measure α) : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ
    then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + (ν .univ).toReal - (μ .univ).toReal)
    else ∞

lemma kl_of_ac_of_integrable (h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) :
    kl μ ν = ENNReal.ofReal (∫ x, llr μ ν x ∂μ + (ν .univ).toReal - (μ .univ).toReal) :=
  if_pos ⟨h1, h2⟩

@[simp]
lemma kl_of_not_ac (h : ¬ μ ≪ ν) : kl μ ν = ∞ := if_neg (not_and_of_not_left _ h)

@[simp]
lemma kl_of_not_integrable (h : ¬ Integrable (llr μ ν) μ) : kl μ ν = ∞ :=
  if_neg (not_and_of_not_right _ h)

/-- If `μ ≪ ν` and `μ univ = ν univ`, then `toReal` of the Kullback-Leibler divergence is equal to
an integral, without any integrability condition. Not true in general without `μ ≪ ν`,
as the integral might be finite but non-zero. -/
lemma kl_toReal_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ≪ ν)
    (h_eq : μ univ = ν univ) :
    (kl μ ν).toReal = ∫ a, llr μ ν a ∂μ + (ν .univ).toReal - (μ .univ).toReal := by
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [kl_of_ac_of_integrable h h_int, ENNReal.toReal_ofReal]
    exact integral_llr_add_sub_measure_univ_nonneg h h_int
  · rw [kl_of_not_integrable h_int, integral_undef h_int]
    simp [h_eq]

-- lemma derivAtTop_mul_log : derivAtTop (fun x ↦ x * log x) = ⊤ :=
--   derivAtTop_of_tendsto_atTop tendsto_mul_log_atTop

@[simp]
lemma kl_self (μ : Measure α) [SigmaFinite μ] : kl μ μ = 0 := by
  have h := llr_self μ
  rw [kl, if_pos]
  · simp [integral_congr_ae h]
  · rw [integrable_congr h]
    exact ⟨Measure.AbsolutelyContinuous.rfl, integrable_zero _ _ μ⟩

@[simp]
lemma kl_zero_left [IsFiniteMeasure ν] : kl 0 ν = ν .univ := by
  convert kl_of_ac_of_integrable (Measure.AbsolutelyContinuous.zero _) integrable_zero_measure
  simp [integral_zero_measure, EReal.coe_zero]

@[simp]
lemma kl_zero_right [NeZero μ] : kl μ 0 = ∞ :=
  kl_of_not_ac (Measure.absolutelyContinuous_zero_iff.mp.mt (NeZero.ne _))

lemma kl_eq_top_iff : kl μ ν = ∞ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ := by
  constructor <;> intro h <;> push_neg at *
  · contrapose! h
    rw [kl_of_ac_of_integrable h.1 h.2]
    simp only [ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]
  · rcases or_not_of_imp h with (h | h) <;> simp [h]

lemma kl_ne_top_iff : kl μ ν ≠ ∞ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ := by
  rw [ne_eq, kl_eq_top_iff]
  push_neg
  rfl

lemma kl_ne_top_iff' :
    kl μ ν ≠ ∞
      ↔ kl μ ν = ENNReal.ofReal (∫ x, llr μ ν x ∂μ + (ν .univ).toReal - (μ .univ).toReal) := by
  constructor
  · rw [kl_ne_top_iff]
    rintro ⟨h1, h2⟩
    rw [kl_of_ac_of_integrable h1 h2]
  · intro h
    rw [h]
    simp

open Classical in
lemma kl_eq_integral [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ
      then ENNReal.ofReal (∫ x, (fun y ↦ y * log y + 1 - y) ((∂μ/∂ν) x).toReal ∂ν)
      else ∞ := by
  rw [kl]
  refine if_ctx_congr Iff.rfl (fun h ↦ ?_) fun _ ↦ rfl
  rw [todo_integral h.1 h.2]

-- @[simp]
-- lemma kl_ne_bot (μ ν : Measure α) : kl μ ν ≠ ⊥ := by
--   rw [kl]
--   split_ifs with h
--   · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
--   · norm_num

lemma fDiv_mul_log_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv klDivFun μ ν = ∞ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ := by
  rw [fDiv_eq_top_iff]
  simp only [derivAtTop_klDivFun, true_and]
  by_cases hμν : μ ≪ ν
  · rw [lintegral_klDivFun_eq_top_iff hμν]
    tauto
  · simp [hμν]

lemma kl_eq_fDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ ν = fDiv klDivFun μ ν := by
  classical
  by_cases hμν : μ ≪ ν
  swap; · rw [fDiv_of_not_ac derivAtTop_klDivFun hμν, kl_of_not_ac hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [fDiv_of_derivAtTop_eq_top derivAtTop_klDivFun, kl_of_ac_of_integrable hμν h_int,
      if_pos hμν]
    exact (lintegral_klDivFun_eq_integral hμν h_int).symm
  · rw [kl_of_not_integrable h_int, fDiv_of_lintegral_eq_top]
    exact lintegral_klDivFun_of_not_integrable hμν h_int

lemma measurable_kl {β : Type*} [MeasurableSpace β] [CountableOrCountablyGenerated α β]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦ kl (κ a) (η a)) := by
  simp_rw [kl_eq_fDiv]
  exact measurable_fDiv _ _

section kl_nonneg

lemma kl_ge_mul_log' [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    ENNReal.ofReal ((μ univ).toReal * log (μ univ).toReal + 1 - (μ univ).toReal) ≤ kl μ ν := by
  calc
  _ = klDivFun (μ univ) := by rw [klDivFun_apply (measure_ne_top _ _)]
  _ ≤ _ := by
    refine (le_fDiv_of_ac hμν ?_).trans_eq kl_eq_fDiv.symm
    intro x hx
    simp [klDivFun_apply hx]

lemma kl_ge_mul_log (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal.ofReal ((μ univ).toReal * log ((μ univ).toReal / (ν univ).toReal)
        + (ν univ).toReal - (μ univ).toReal)
      ≤ kl μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [h_int]
  rw [kl_of_ac_of_integrable hμν h_int]
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  have : NeZero ν := ⟨hν⟩
  let ν' := (ν .univ)⁻¹ • ν
  have hμν' : μ ≪ ν' :=
    Measure.AbsolutelyContinuous.trans hμν (Measure.absolutelyContinuous_smul (by simp))
  have h := kl_ge_mul_log' hμν'
  rw [kl_of_ac_of_integrable hμν',
    integral_congr_ae (llr_smul_right hμν (ν .univ)⁻¹ (by simp) (by simp [hν]))] at h
  swap
  · rw [integrable_congr (llr_smul_right hμν (ν .univ)⁻¹ (by simp) (by simp [hν]))]
    exact h_int.sub (integrable_const _)
  rw [log_div, mul_sub]
  rotate_left
  · simp [ENNReal.toReal_eq_zero_iff, hμ]
  · simp [ENNReal.toReal_eq_zero_iff, hν]
  simp only [ENNReal.toReal_inv, log_inv, sub_neg_eq_add, measure_univ, ENNReal.one_toReal,
    add_le_add_iff_right] at h
  rw [ENNReal.ofReal_le_ofReal_iff'] at h
  cases h with
  | inl h =>
    gcongr
    rw [integral_add h_int (integrable_const _), integral_const, smul_eq_mul,
      sub_le_sub_iff_right, add_le_add_iff_right] at h
    rw [sub_le_iff_le_add]
    exact h
  | inr h =>
    have h' : (μ univ).toReal * log (μ univ).toReal + 1 - (μ univ).toReal = 0 :=
      le_antisymm h (mul_log_add_one_sub_nonneg ENNReal.toReal_nonneg)
    have h'' : (μ univ).toReal = 1 := (mul_log_add_one_sub_eq_zero_iff (by simp)).mp h'
    simp [h'']
    have h_eq := integral_llr_add_mul_log_nonneg hμν h_int
    simp only [h'', one_mul, add_sub_cancel_right] at h_eq
    rw [ENNReal.ofReal_le_ofReal_iff]
    swap
    · refine h_eq.trans ?_
      rw [add_sub_assoc]
      gcongr
      exact log_le_sub_one_of_pos (by simp [ENNReal.toReal_pos_iff, hν])
    rw [sub_le_sub_iff_right, add_le_add_iff_right]
    linarith

-- lemma kl_nonneg' (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (h : μ .univ ≥ ν .univ) :
--     0 ≤ kl μ ν := by
--   by_cases hμν : μ ≪ ν
--   swap; · rw [kl_of_not_ac hμν]; simp
--   by_cases h_int : Integrable (llr μ ν) μ
--   swap; · rw [kl_of_not_integrable h_int]; simp
--   calc 0
--     ≤ ((μ .univ).toReal : EReal) * log ((μ .univ).toReal / (ν .univ).toReal) := by
--         by_cases h_zero : NeZero ν
--         swap; · simp [not_neZero.mp h_zero]
--         refine mul_nonneg (EReal.coe_nonneg.mpr ENNReal.toReal_nonneg) ?_
--         norm_cast
--         refine log_nonneg ((one_le_div ?_).mpr ?_)
--         · exact ENNReal.toReal_pos (NeZero.ne' _).symm (measure_ne_top _ _)
--         · gcongr
--           exact measure_ne_top _ _
--   _ ≤ kl μ ν := kl_ge_mul_log _ _

-- /-- **Gibbs' inequality**: the Kullback-Leibler divergence between two probability distributions is
-- nonnegative. -/
-- lemma kl_nonneg (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
--     0 ≤ kl μ ν := kl_nonneg' μ ν (by simp)

/-- **Converse Gibbs' inequality**: the Kullback-Leibler divergence between two finite measures is
zero if and only if the two distributions are equal. -/
lemma kl_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ ν = 0 ↔ μ = ν := by
  refine kl_eq_fDiv (μ := μ) (ν := ν) ▸ fDiv_eq_zero_iff derivAtTop_klDivFun ?_
  exact strictConvexOn_klDivFun

-- /-- **Converse Gibbs' inequality**: the Kullback-Leibler divergence between two probability
-- distributions is zero if and only if the two distributions are equal. -/
-- lemma kl_eq_zero_iff' [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
--     kl μ ν = 0 ↔ μ = ν := kl_eq_zero_iff

end kl_nonneg

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β}

lemma kl_comp_le_compProd [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    kl (κ ∘ₘ μ) (η ∘ₘ ν) ≤ kl (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simp_rw [kl_eq_fDiv]
  exact fDiv_comp_le_compProd μ ν κ η

/--The **Data Processing Inequality** for the Kullback-Leibler divergence. -/
lemma kl_comp_right_le [Nonempty α] [StandardBorelSpace α] [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    kl (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ kl μ ν := by
  simp_rw [kl_eq_fDiv]
  exact fDiv_comp_right_le μ ν κ

end DataProcessingInequality

end ProbabilityTheory

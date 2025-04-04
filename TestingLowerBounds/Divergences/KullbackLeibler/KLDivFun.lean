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

@[simp]
lemma rightDeriv_neg {y : ℝ} : rightDeriv (fun x ↦ - x) y = - 1 :=
  rightDeriv_of_hasDerivAt (hasDerivAt_neg _)

lemma _root_.convexOn_mul_log_add_one_sub :
    ConvexOn ℝ (Ici 0) fun x ↦ x * log x + 1 - x :=
  (convexOn_mul_log.add (convexOn_const _ (convex_Ici _))).sub (concaveOn_id (convex_Ici _))

lemma strictConvexOn_mul_log_add_one_sub :
    StrictConvexOn ℝ (Ici 0) fun x ↦ x * log x + 1 - x := by
  simp_rw [add_sub_assoc]
  refine strictConvexOn_mul_log.add_convexOn ?_
  exact (convexOn_const _ (convex_Ici _)).sub (concaveOn_id (convex_Ici _))

lemma hasDerivAt_mul_log_add_one_sub {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x ↦ x * log x + 1 - x) (log x) x := by
  convert ((hasDerivAt_mul_log hx).add (hasDerivAt_const x 1)).sub (hasDerivAt_id x) using 1
  ring

@[simp]
lemma rightDeriv_mul_log_add_one_sub {x : ℝ} (hx : x ≠ 0) :
    rightDeriv (fun x ↦ x * log x + 1 - x) x = log x :=
  rightDeriv_of_hasDerivAt (hasDerivAt_mul_log_add_one_sub hx)

lemma rightDeriv_mul_log_add_one_sub_eventually_eq :
    rightDeriv (fun x ↦ x * log x + 1 - x) =ᶠ[atTop] log := by
  filter_upwards [eventually_ne_atTop 0] with x hx
  rw [rightDeriv_mul_log_add_one_sub hx]

lemma mul_log_add_one_sub_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x * log x + 1 - x := by
  rcases hx.eq_or_lt with rfl | hx; · simp
  refine ConvexOn.nonneg_of_todo (f := fun x ↦ x * log x + 1 - x) ?_ ?_ ?_ hx
  · exact convexOn_mul_log_add_one_sub.subset (Ioi_subset_Ici le_rfl) (convex_Ioi _)
  · simp
  · simp

-- unused?
lemma mul_log_add_one_sub_eq_zero_iff {x : ℝ} (hx : 0 ≤ x) : x * log x + 1 - x = 0 ↔ x = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  refine strictConvexOn_mul_log_add_one_sub.eq_of_isMinOn
    (isMinOn_iff.mpr fun y hy ↦ h ▸ mul_log_add_one_sub_nonneg hy) (isMinOn_iff.mpr fun y hy ↦ ?_)
    hx (zero_le_one' ℝ)
  rw [log_one, mul_zero, zero_add, sub_self]
  exact mul_log_add_one_sub_nonneg hy

lemma integrable_mul_log_add_one_sub_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    Integrable (fun x ↦ ((∂μ/∂ν) x).toReal * log ((∂μ/∂ν) x).toReal + 1 - ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (llr μ ν) μ := by
  suffices
      Integrable (fun x ↦ ((∂μ/∂ν) x).toReal * log ((∂μ/∂ν) x).toReal + (1 - ((∂μ/∂ν) x).toReal)) ν
      ↔ Integrable (llr μ ν) μ by
    convert this using 3 with x
    rw [add_sub_assoc]
  rw [integrable_add_iff_integrable_left']
  · rw [integrable_rnDeriv_mul_log_iff hμν]
  · refine (integrable_const _).sub ?_
    exact Measure.integrable_toReal_rnDeriv

lemma tendsto_mul_log_add_one_sub_atTop : Tendsto (fun x ↦ x * log x + 1 - x) atTop atTop := by
  have : (fun x ↦ x * log x + 1 - x) = (fun x ↦ x * (log x - 1) + 1) := by ext; ring
  rw [this]
  refine Tendsto.atTop_add ?_ tendsto_const_nhds
  refine Tendsto.atTop_mul_atTop ?_ ?_
  · exact fun _ a ↦ a
  · exact tendsto_log_atTop.atTop_add tendsto_const_nhds

lemma continuous_mul_log_add_one_sub : Continuous (fun x ↦ x * log x + 1 - x) := by fun_prop

end MulLog

section KLDivFun

noncomputable
def klDivFun : DivFunction := DivFunction.ofReal (fun x ↦ x * log x + 1 - x)
  (convexOn_mul_log_add_one_sub.subset (Set.Ioi_subset_Ici le_rfl) (convex_Ioi _))
  (by simp)

@[simp] lemma klDivFun_apply_top : klDivFun ∞ = ∞ := by
  rw [klDivFun, DivFunction.ofReal_apply_top_of_tendsto_atTop]
  exact tendsto_mul_log_add_one_sub_atTop

lemma klDivFun_apply {x : ℝ≥0∞} (hx : x ≠ ∞) :
    klDivFun x = ENNReal.ofReal (x.toReal * log x.toReal + 1 - x.toReal) := by
  by_cases hx0 : x = 0
  · rw [klDivFun, hx0, DivFunction.ofReal_apply_zero_of_continuousWithinAt]
    simp only [log_zero, mul_zero, zero_add, sub_zero, ENNReal.ofReal_one, ENNReal.zero_toReal]
    exact continuous_mul_log_add_one_sub.continuousWithinAt
  · rw [klDivFun, DivFunction.ofReal_apply hx0 hx]

@[simp]
lemma klDivFun_zero : klDivFun 0 = 1 := by simp [klDivFun_apply ENNReal.zero_ne_top]

@[simp]
lemma klDivFun_realFun_apply {x : ℝ} (hx : 0 ≤ x) : klDivFun.realFun x = x * log x + 1 - x := by
  rw [DivFunction.realFun, klDivFun_apply ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hx,
    ENNReal.toReal_ofReal]
  exact mul_log_add_one_sub_nonneg hx

@[simp] lemma derivAtTop_klDivFun : klDivFun.derivAtTop = ∞ := by
  refine DivFunction.derivAtTop_ofReal_of_tendsto_atTop ?_
  rw [tendsto_congr' rightDeriv_mul_log_add_one_sub_eventually_eq]
  exact tendsto_log_atTop

lemma eqOn_klDivFun_realFun : EqOn klDivFun.realFun (fun x ↦ x * log x + 1 - x) (Ici 0) :=
  fun _ hx ↦ klDivFun_realFun_apply hx

lemma strictConvexOn_klDivFun : StrictConvexOn ℝ (Ici 0) klDivFun.realFun :=
  StrictConvexOn.congr strictConvexOn_mul_log_add_one_sub eqOn_klDivFun_realFun.symm

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
  rw [klDivFun]
  refine DivFunction.lintegral_ofReal_eq_top_of_not_integrable ?_ ?_
  · exact fun x ↦ mul_log_add_one_sub_nonneg
  · rwa [integrable_mul_log_add_one_sub_iff hμν]

lemma lintegral_klDivFun_eq_integral [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    ∫⁻ x, klDivFun (μ.rnDeriv ν x) ∂ν
      = ENNReal.ofReal (∫ x, llr μ ν x ∂μ + (ν .univ).toReal - (μ .univ).toReal) := by
  rw [klDivFun, DivFunction.lintegral_ofReal_eq_integral_of_continuous, todo_integral hμν h_int]
  · exact fun x ↦ mul_log_add_one_sub_nonneg
  · exact continuous_mul_log_add_one_sub.continuousWithinAt
  · rwa [integrable_mul_log_add_one_sub_iff hμν]

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

end ProbabilityTheory

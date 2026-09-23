/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.InformationTheory.KullbackLeibler.Basic
import TestingLowerBounds.FDiv.CompProd.CompProd
import TestingLowerBounds.FDiv.Measurable

/-!
# The divergence function of the Kullback-Leibler divergence

`klDivFun` is the `DivFunction` obtained from Mathlib's `InformationTheory.klFun`,
`x ↦ x * log x + 1 - x`.

-/

open Real MeasureTheory Filter MeasurableSpace Set InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

@[simp]
lemma rightDeriv_neg {y : ℝ} : rightDeriv (fun x ↦ - x) y = - 1 :=
  rightDeriv_of_hasDerivAt (hasDerivAt_neg _)

section KLDivFun

/-- The `DivFunction` of the Kullback-Leibler divergence, `x ↦ x * log x + 1 - x` on `[0, ∞)`. -/
noncomputable
def klDivFun : DivFunction := DivFunction.ofReal klFun convexOn_Ioi_klFun klFun_one

@[simp] lemma klDivFun_apply_top : klDivFun ∞ = ∞ := by
  rw [klDivFun, DivFunction.ofReal_apply_top_of_tendsto_atTop]
  exact tendsto_klFun_atTop

lemma klDivFun_apply {x : ℝ≥0∞} (hx : x ≠ ∞) :
    klDivFun x = ENNReal.ofReal (x.toReal * log x.toReal + 1 - x.toReal) := by
  by_cases hx0 : x = 0
  · rw [klDivFun, hx0, DivFunction.ofReal_apply_zero_of_continuousWithinAt]
    · simp [klFun_zero]
    · exact continuous_klFun.continuousWithinAt
  · rw [klDivFun, DivFunction.ofReal_apply hx0 hx, klFun_apply]

@[simp]
lemma klDivFun_zero : klDivFun 0 = 1 := by simp [klDivFun_apply ENNReal.zero_ne_top]

@[simp]
lemma klDivFun_realFun_apply {x : ℝ} (hx : 0 ≤ x) : klDivFun.realFun x = x * log x + 1 - x := by
  rw [DivFunction.realFun, klDivFun_apply ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hx,
    ENNReal.toReal_ofReal]
  exact klFun_nonneg hx

@[simp] lemma derivAtTop_klDivFun : klDivFun.derivAtTop = ∞ := by
  refine DivFunction.derivAtTop_ofReal_of_tendsto_atTop (fun x hx ↦ klFun_nonneg hx.le) ?_
  exact tendsto_rightDeriv_klFun_atTop

lemma eqOn_klDivFun_realFun : EqOn klDivFun.realFun (fun x ↦ x * log x + 1 - x) (Ici 0) :=
  fun _ hx ↦ klDivFun_realFun_apply hx

lemma strictConvexOn_klDivFun : StrictConvexOn ℝ (Ici 0) klDivFun.realFun :=
  StrictConvexOn.congr strictConvexOn_klFun eqOn_klDivFun_realFun.symm

lemma lintegral_klDivFun_rnDeriv [SigmaFinite μ] :
    ∫⁻ x, klDivFun (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x, ENNReal.ofReal ((μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal
        + 1 - (μ.rnDeriv ν x).toReal) ∂ν := by
  have h_ne_top := μ.rnDeriv_ne_top ν
  refine lintegral_congr_ae ?_
  filter_upwards [h_ne_top] with x hx
  rw [klDivFun_apply hx]

lemma lintegral_klDivFun_of_not_integrable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : ¬ Integrable (llr μ ν) μ) :
    ∫⁻ x, klDivFun (μ.rnDeriv ν x) ∂ν = ∞ := by
  rw [klDivFun]
  refine DivFunction.lintegral_ofReal_eq_top_of_not_integrable ?_ ?_
  · exact fun x ↦ klFun_nonneg
  · rwa [integrable_klFun_rnDeriv_iff hμν]

lemma lintegral_klDivFun_eq_integral [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    ∫⁻ x, klDivFun (μ.rnDeriv ν x) ∂ν
      = ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ) := by
  rw [klDivFun, DivFunction.lintegral_ofReal_eq_integral_of_continuous,
    integral_klFun_rnDeriv hμν h_int]
  · exact fun x ↦ klFun_nonneg
  · exact continuous_klFun.continuousWithinAt
  · rwa [integrable_klFun_rnDeriv_iff hμν]

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

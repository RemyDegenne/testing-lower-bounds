/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import TestingLowerBounds.Divergences.StatInfo.StatInfo
import TestingLowerBounds.Divergences.StatInfo.DivFunction
import TestingLowerBounds.FDiv.Measurable
import TestingLowerBounds.FDiv.DivFunction.CurvatureMeasure
import TestingLowerBounds.FDiv.Basic

/-!
# fDiv and StatInfo

-/

open MeasureTheory Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞} {π : Measure Bool} {f : DivFunction} {β γ x t : ℝ}

section StatInfoFun

open Set Filter ConvexOn

lemma measurable_fDiv_statInfoFun (μ ν : Measure 𝒳) [SigmaFinite μ] [SFinite ν] :
    Measurable (Function.uncurry fun β γ ↦ fDiv (statInfoDivFun β γ) μ ν) := by
  simp_rw [fDiv]
  · refine Measurable.add ?_ ?_
    · exact measurable_lintegral_statInfoDivFun
    simp_rw [derivAtTop_statInfoDivFun_eq]
    refine Measurable.mul_const ?_ _
    apply Measurable.ite (measurableSet_le measurable_const measurable_fst)
      <;> refine Measurable.ite (measurableSet_le measurable_snd measurable_fst) ?_ ?_ <;> fun_prop

lemma stronglyMeasurable_fDiv_statInfoFun (μ ν : Measure 𝒳) [SigmaFinite μ] [SFinite ν] :
    StronglyMeasurable (Function.uncurry fun β γ ↦ fDiv (statInfoDivFun β γ) μ ν) :=
  (measurable_fDiv_statInfoFun μ ν).stronglyMeasurable

section FDivStatInfo

lemma fDiv_statInfoFun_eq_integral_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv (statInfoDivFun β γ) μ ν
      = ENNReal.ofReal (∫ x, statInfoFun β γ ((∂μ/∂ν) x).toReal ∂ν)
        + (statInfoDivFun β γ).derivAtTop * μ.singularPart ν univ := by
  unfold statInfoDivFun
  rw [fDiv_ofReal_eq_integral_add]
  · exact fun _ _ ↦ statInfoFun_nonneg _ _ _
  · exact continuousWithinAt_statInfoFun_zero
  · exact integrable_statInfoFun_rnDeriv _ _ _ _

lemma fDiv_statInfoFun_eq_integral_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    fDiv (statInfoDivFun β γ) μ ν
      = ENNReal.ofReal (∫ x, statInfoFun β γ ((∂μ/∂ν) x).toReal ∂ν) := by
  rw [fDiv_statInfoFun_eq_integral_add, Measure.singularPart_eq_zero_of_ac hμν]
  simp

lemma fDiv_statInfoFun_eq_lintegral_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    fDiv (statInfoDivFun β γ) μ ν
      = ∫⁻ x, ENNReal.ofReal (statInfoFun β γ ((∂μ/∂ν) x).toReal) ∂ν := by
  unfold statInfoDivFun
  rw [fDiv_ofReal_eq_lintegral_of_ac _ _ _ hμν]
  · exact fun _ _ ↦ statInfoFun_nonneg _ _ _
  · exact continuousWithinAt_statInfoFun_zero
  · exact integrable_statInfoFun_rnDeriv _ _ _ _

lemma toReal_fDiv_statInfoFun_eq_integral_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = ∫ x, statInfoFun β γ ((∂μ/∂ν) x).toReal ∂ν
        + (statInfoDivFun β γ).derivAtTop.toReal * (μ.singularPart ν univ).toReal := by
  unfold statInfoDivFun
  rw [toReal_fDiv_ofReal_eq_integral_add']
  · exact fun _ _ ↦ statInfoFun_nonneg _ _ _
  · exact continuousWithinAt_statInfoFun_zero
  · exact integrable_statInfoFun_rnDeriv _ _ _ _
  · exact derivAtTop_statInfoDivFun_ne_top _ _

lemma fDiv_statInfoDivFun_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv (statInfoDivFun β γ) μ ν ≠ ∞ := by
  refine fDiv_ne_top_of_derivAtTop_ne_top ?_ (derivAtTop_statInfoDivFun_ne_top _ _)
  unfold statInfoDivFun
  simp [DivFunction.ofReal_apply_zero_of_continuousWithinAt continuousWithinAt_statInfoFun_zero]

lemma fDiv_statInfoFun_eq_integral_max_of_nonneg_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν := by
  simp_rw [toReal_fDiv_statInfoFun_eq_integral_add, derivAtTop_statInfoDivFun_of_nonneg_of_le hβ hγ,
    ENNReal.toReal_zero, zero_mul, add_zero, statInfoFun_of_le hγ]

lemma fDiv_statInfoFun_eq_integral_max_of_nonneg_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : β < γ) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν + β * (μ.singularPart ν univ).toReal := by
  simp_rw [toReal_fDiv_statInfoFun_eq_integral_add, derivAtTop_statInfoDivFun_of_nonneg_of_gt hβ hγ,
    statInfoFun_of_gt hγ, ENNReal.toReal_ofReal hβ]

lemma fDiv_statInfoFun_eq_integral_max_of_nonpos_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : γ ≤ β) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν
        - β * (μ.singularPart ν univ).toReal := by
  simp_rw [toReal_fDiv_statInfoFun_eq_integral_add, derivAtTop_statInfoDivFun_of_nonpos_of_le hβ hγ,
    statInfoFun_of_le hγ]
  rw [ENNReal.toReal_ofReal, sub_eq_add_neg, neg_mul]
  simp [hβ]

lemma fDiv_statInfoFun_eq_integral_max_of_nonpos_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : β < γ) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν := by
  simp_rw [toReal_fDiv_statInfoFun_eq_integral_add,
    derivAtTop_statInfoDivFun_of_nonpos_of_gt hβ hγ, statInfoFun_of_gt hγ, ENNReal.toReal_zero,
    zero_mul, add_zero]

lemma fDiv_statInfoFun_eq_zero_of_nonneg_of_nonpos [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : γ ≤ 0) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal = 0 := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonneg_of_le hβ (hγ.trans hβ)]
  convert integral_zero 𝒳 ℝ with x
  exact max_eq_left <| tsub_nonpos.mpr <| hγ.trans <| mul_nonneg hβ ENNReal.toReal_nonneg

lemma fDiv_statInfoFun_eq_zero_of_nonpos_of_pos [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : 0 < γ) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal = 0 := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonpos_of_gt hβ (hβ.trans_lt hγ)]
  convert integral_zero 𝒳 ℝ with x
  exact max_eq_left <| tsub_nonpos.mpr <|
    (mul_nonpos_iff.mpr <| Or.inr ⟨hβ, ENNReal.toReal_nonneg⟩).trans hγ.le

/-- Auxiliary lemma for `fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_le` and
`fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_le`. -/
lemma integral_max_eq_integral_abs [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν
      = 2⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν + γ * (ν univ).toReal - β * (μ univ).toReal
        + β * ((μ.singularPart ν) univ).toReal) := by
  simp_rw [max_eq_add_add_abs_sub, zero_add, zero_sub, neg_sub, integral_const_mul]
  congr
  have h_int : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have h_int' : Integrable (fun x ↦ γ - β * ((∂μ/∂ν) x).toReal) ν := (integrable_const γ).sub h_int
  rw [integral_add h_int', integral_sub (integrable_const γ) h_int, integral_const, smul_eq_mul,
    mul_comm, integral_const_mul, add_comm, add_sub_assoc, add_assoc, sub_eq_add_neg,
    sub_eq_add_neg, add_assoc, ← mul_neg, ← mul_neg, ← mul_add]
  swap; · exact (integrable_add_const_iff.mpr h_int).abs
  congr
  nth_rw 2 [μ.haveLebesgueDecomposition_add ν]
  simp only [Measure.coe_add, Pi.add_apply, MeasurableSet.univ, withDensity_apply,
    Measure.restrict_univ]
  rw [ENNReal.toReal_add (measure_ne_top _ _)]
  swap; · exact lt_top_iff_ne_top.mp <| (setLIntegral_univ _ ▸
    Measure.setLIntegral_rnDeriv_le univ).trans_lt IsFiniteMeasure.measure_univ_lt_top
  ring_nf
  rw [integral_toReal (μ.measurable_rnDeriv ν).aemeasurable (μ.rnDeriv_lt_top ν)]

/-- Auxiliary lemma for `fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_gt` and
`fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_gt`. -/
lemma integral_max_eq_integral_abs' [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν
      = 2⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν - γ * (ν univ).toReal + β * (μ univ).toReal
        - β * ((μ.singularPart ν) univ).toReal) := by
  simp_rw [max_eq_add_add_abs_sub, zero_add, zero_sub, abs_neg, integral_const_mul]
  congr
  have h_int : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have h_int' : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal - γ) ν := h_int.sub (integrable_const γ)
  rw [integral_add h_int', integral_sub h_int (integrable_const γ), integral_const, smul_eq_mul,
    mul_comm, integral_const_mul, add_comm, add_sub_assoc, sub_eq_add_neg, add_comm (β * _),
    ← add_assoc, ← sub_eq_add_neg]
  swap; · exact (h_int.sub (integrable_const _)).abs
  congr
  nth_rw 2 [μ.haveLebesgueDecomposition_add ν]
  simp only [Measure.coe_add, Pi.add_apply, MeasurableSet.univ, withDensity_apply,
    Measure.restrict_univ]
  rw [ENNReal.toReal_add (measure_ne_top _ _)]
  swap; · exact lt_top_iff_ne_top.mp <| (setLIntegral_univ _ ▸
    Measure.setLIntegral_rnDeriv_le univ).trans_lt IsFiniteMeasure.measure_univ_lt_top
  ring_nf
  rw [integral_toReal (μ.measurable_rnDeriv ν).aemeasurable (μ.rnDeriv_lt_top ν)]

lemma fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
        + β * (μ.singularPart ν univ).toReal + γ * (ν univ).toReal - β * (μ univ).toReal) := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonneg_of_le hβ hγ, integral_max_eq_integral_abs,
    sub_eq_add_neg, add_assoc, add_comm (- _), ← add_assoc, ← sub_eq_add_neg, add_assoc,
    add_comm (_ * _), add_assoc]

lemma fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : β < γ) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      + β * (μ.singularPart ν univ).toReal + β * (μ univ).toReal - γ * (ν univ).toReal) := by
  have h_eq : β * (μ.singularPart ν univ).toReal
      = 2⁻¹ * (2 * β * (μ.singularPart ν univ).toReal) := by simp [mul_assoc]
  rw [fDiv_statInfoFun_eq_integral_max_of_nonneg_of_gt hβ hγ, integral_max_eq_integral_abs', h_eq,
    ← mul_add]
  simp_rw [sub_eq_add_neg, add_assoc]
  congr 2
  ring

lemma fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : γ ≤ β) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      - β * (μ.singularPart ν univ).toReal + γ * (ν univ).toReal - β * (μ univ).toReal) := by
  have h_eq : β * (μ.singularPart ν univ).toReal
      = 2⁻¹ * (2 * β * ((μ.singularPart ν) univ).toReal) := by simp [mul_assoc]
  rw [fDiv_statInfoFun_eq_integral_max_of_nonpos_of_le hβ hγ, integral_max_eq_integral_abs, h_eq,
    sub_eq_add_neg, ← mul_neg, ← mul_add]
  simp_rw [sub_eq_add_neg, add_assoc]
  congr 2
  ring

lemma fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : β < γ) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      - β * (μ.singularPart ν univ).toReal + β * (μ univ).toReal - γ * (ν univ).toReal) := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonpos_of_gt hβ hγ, integral_max_eq_integral_abs']
  simp_rw [sub_eq_add_neg]
  ring_nf

end FDivStatInfo

section FDivStatInfoEqStatInfo

lemma fDiv_statInfoFun_eq_StatInfo_of_nonneg_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hγβ : γ ≤ β) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = (statInfo μ ν (Bool.boolMeasure (.ofReal β) (.ofReal γ))).toReal
        + 2⁻¹ * (|β * (μ univ).toReal - γ * (ν univ).toReal|
        + γ * (ν univ).toReal - β * (μ univ).toReal) := by
  rw [toReal_statInfo_eq_integral_abs]
  simp only [Bool.boolMeasure_apply_false, ENNReal.toReal_mul, hβ, ENNReal.toReal_ofReal,
    Bool.boolMeasure_apply_true, hγ]
  rw [fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_le hβ hγβ, ← mul_add]
  simp_rw [sub_eq_add_neg, ← add_assoc]
  rw [add_comm (-_ + _ + _)]
  simp_rw [← add_assoc, ← sub_eq_add_neg, sub_self, zero_add]

lemma fDiv_statInfoFun_eq_StatInfo_of_nonneg_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hγβ : β < γ) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = (statInfo μ ν (Bool.boolMeasure (.ofReal β) (.ofReal γ))).toReal
        + 2⁻¹ * (|β * (μ univ).toReal - γ * (ν univ).toReal|
        + β * (μ univ).toReal - γ * (ν univ).toReal) := by
  rw [toReal_statInfo_eq_integral_abs]
  simp only [Bool.boolMeasure_apply_false, ENNReal.toReal_mul, hβ, ENNReal.toReal_ofReal,
    Bool.boolMeasure_apply_true, hγ]
  rw [fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_gt hβ hγβ, ← mul_add]
  simp_rw [sub_eq_add_neg, ← add_assoc]
  rw [add_comm (-_ + _ + _)]
  simp_rw [← add_assoc, ← sub_eq_add_neg, sub_self, zero_add]

-- N.B. we cannot use the Real.sign function here because it is 0 at 0, but we need it to be -1.
lemma fDiv_statInfoFun_eq_StatInfo_of_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    (fDiv (statInfoDivFun β γ) μ ν).toReal
      = (statInfo μ ν (Bool.boolMeasure (.ofReal β) (.ofReal γ))).toReal
        + 2⁻¹ * (|β * (μ univ).toReal - γ * (ν univ).toReal|
        + (if γ ≤ β then -1 else 1) * (β * (μ univ).toReal - γ * (ν univ).toReal)) := by
  rcases le_or_gt γ β with (hβγ | hβγ)
  · rw [fDiv_statInfoFun_eq_StatInfo_of_nonneg_of_le hβ hγ hβγ, ite_eq_left hβγ, neg_one_mul,
      neg_sub, sub_eq_add_neg, add_assoc, ← sub_eq_add_neg]
  · rw [fDiv_statInfoFun_eq_StatInfo_of_nonneg_of_gt hβ hγ hβγ, ite_eq_right hβγ.not_ge, one_mul,
      add_sub_assoc]

end FDivStatInfoEqStatInfo

end StatInfoFun

end ProbabilityTheory

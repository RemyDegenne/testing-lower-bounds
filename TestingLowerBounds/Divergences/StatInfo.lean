/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.CurvatureMeasure
import TestingLowerBounds.StatInfoFun
import Mathlib.Order.CompletePartialOrder
import TestingLowerBounds.FDiv.Basic
import TestingLowerBounds.Testing.Binary
import Mathlib.MeasureTheory.Constructions.Prod.Integral

/-!
# Statistical information

## Main definitions

* `statInfo`

## Main statements

* `statInfo_comp_le`: data-processing inequality

## Notation

## Implementation details

-/

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞} (π : Measure Bool)

-- TODO: replace the min by a risk
/-- The statistical information of the measures `μ` and `ν` with respect to
the prior `π ∈ ℳ({0,1})`. -/
noncomputable
def statInfo (μ ν : Measure 𝒳) (π : Measure Bool) : ℝ≥0∞ :=
  min (π {false} * μ Set.univ) (π {true} * μ Set.univ) - bayesBinaryRisk μ ν π

/-- **Data processing inequality** for the statistical information. -/
lemma statInfo_comp_le (μ ν : Measure 𝒳) (π : Measure Bool) (η : kernel 𝒳 𝒳') [IsMarkovKernel η] :
    statInfo (μ ∘ₘ η) (ν ∘ₘ η) π ≤ statInfo μ ν π := by
  refine tsub_le_tsub ?_ (bayesBinaryRisk_le_bayesBinaryRisk_comp _ _ _ _)
  rw [Measure.bind_apply MeasurableSet.univ (kernel.measurable _)]
  simp

section StatInfoFun

open Set Filter ConvexOn

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳} {f : ℝ → ℝ} {β γ x t : ℝ}

lemma integrable_statInfoFun_rnDeriv (β γ : ℝ)
    (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x ↦ statInfoFun β γ ((∂μ/∂ν) x).toReal) ν := by
  refine integrable_f_rnDeriv_of_derivAtTop_ne_top _ _ stronglyMeasurable_statInfoFun3
    ?_ (derivAtTop_statInfoFun_ne_top β γ)
  exact (convexOn_statInfoFun β γ).subset (fun _ _ ↦ trivial) (convex_Ici 0)

lemma nnReal_mul_fDiv {a : NNReal} :
    a * fDiv (statInfoFun β γ) μ ν = fDiv (fun x ↦ statInfoFun (a * β) (a * γ) x) μ ν := by
  change (a.1 : EReal) * _ = _
  rw [← fDiv_mul a.2 ((convexOn_statInfoFun β γ).subset (fun _ _ ↦ trivial) (convex_Ici 0)) μ ν]
  simp_rw [const_mul_statInfoFun a.2]
  rfl

lemma fDiv_statInfoFun_eq_integral_max_of_nonneg_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν = ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν := by
  simp_rw [fDiv_of_integrable (integrable_statInfoFun_rnDeriv _ _ _ _),
    derivAtTop_statInfoFun_of_nonneg_of_le hβ hγ, zero_mul, add_zero, statInfoFun_of_le hγ]

lemma fDiv_statInfoFun_eq_integral_max_of_nonneg_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : β < γ) :
    fDiv (statInfoFun β γ) μ ν
      = ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν + β * (μ.singularPart ν) univ := by
  simp_rw [fDiv_of_integrable (integrable_statInfoFun_rnDeriv _ _ _ _),
    derivAtTop_statInfoFun_of_nonneg_of_gt hβ hγ, statInfoFun_of_gt hγ]

lemma fDiv_statInfoFun_eq_integral_max_of_nonpos_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν
      = ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν - β * (μ.singularPart ν) univ := by
  simp_rw [fDiv_of_integrable (integrable_statInfoFun_rnDeriv _ _ _ _),
    derivAtTop_statInfoFun_of_nonpos_of_le hβ hγ, statInfoFun_of_le hγ, neg_mul, ← sub_eq_add_neg]

lemma fDiv_statInfoFun_eq_integral_max_of_nonpos_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : β < γ) :
    fDiv (statInfoFun β γ) μ ν = ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν := by
  simp_rw [fDiv_of_integrable (integrable_statInfoFun_rnDeriv _ _ _ _),
    derivAtTop_statInfoFun_of_nonpos_of_gt hβ hγ, statInfoFun_of_gt hγ, zero_mul, add_zero]

/-- Auxiliary lemma for `fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_le` and
`fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_le`. -/
lemma integral_max_eq_integral_abs [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν
      = 2⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν + γ * (ν univ).toReal - β * (μ univ).toReal
        + β * ((μ.singularPart ν) univ).toReal) := by
  simp_rw [max_eq_add_add_abs_sub, zero_add, zero_sub, neg_sub, integral_mul_left]
  congr
  have h_int : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have h_int' : Integrable (fun x ↦ γ - β * ((∂μ/∂ν) x).toReal) ν := (integrable_const γ).sub h_int
  rw [integral_add h_int', integral_sub (integrable_const γ) h_int, integral_const, smul_eq_mul,
    mul_comm, integral_mul_left, add_comm, add_sub_assoc, add_assoc, sub_eq_add_neg, sub_eq_add_neg,
    add_assoc, ← mul_neg, ← mul_neg, ← mul_add]
  swap; · exact (integrable_add_const_iff.mpr h_int).abs
  congr
  nth_rw 2 [Measure.haveLebesgueDecomposition_add μ ν]
  simp only [Measure.coe_add, Pi.add_apply, MeasurableSet.univ, withDensity_apply,
    Measure.restrict_univ]
  rw [ENNReal.toReal_add (measure_ne_top _ _)]
  swap; · exact lt_top_iff_ne_top.mp <| (setLIntegral_univ _ ▸
    Measure.setLIntegral_rnDeriv_le univ).trans_lt IsFiniteMeasure.measure_univ_lt_top
  ring_nf
  rw [integral_toReal (Measure.measurable_rnDeriv μ ν).aemeasurable (Measure.rnDeriv_lt_top μ ν)]

/-- Auxiliary lemma for `fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_gt` and
`fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_gt`. -/
lemma integral_max_eq_integral_abs' [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν
      = 2⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν - γ * (ν univ).toReal + β * (μ univ).toReal
        - β * ((μ.singularPart ν) univ).toReal) := by
  simp_rw [max_eq_add_add_abs_sub, zero_add, zero_sub, abs_neg, integral_mul_left]
  congr
  have h_int : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have h_int' : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal - γ) ν := h_int.sub (integrable_const γ)
  rw [integral_add h_int', integral_sub h_int (integrable_const γ), integral_const, smul_eq_mul,
    mul_comm, integral_mul_left, add_comm, add_sub_assoc, sub_eq_add_neg, add_comm (β * _),
    ← add_assoc, ← sub_eq_add_neg]
  swap; · exact (h_int.sub (integrable_const _)).abs
  congr
  nth_rw 2 [Measure.haveLebesgueDecomposition_add μ ν]
  simp only [Measure.coe_add, Pi.add_apply, MeasurableSet.univ, withDensity_apply,
    Measure.restrict_univ]
  rw [ENNReal.toReal_add (measure_ne_top _ _)]
  swap; · exact lt_top_iff_ne_top.mp <| (setLIntegral_univ _ ▸
    Measure.setLIntegral_rnDeriv_le univ).trans_lt IsFiniteMeasure.measure_univ_lt_top
  ring_nf
  rw [integral_toReal (Measure.measurable_rnDeriv μ ν).aemeasurable (Measure.rnDeriv_lt_top μ ν)]

lemma fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      + β * (μ.singularPart ν) univ + γ * ν univ - β * μ univ) := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonneg_of_le hβ hγ, integral_max_eq_integral_abs,
    sub_eq_add_neg, add_assoc, add_comm (- _), ← add_assoc, ← sub_eq_add_neg, add_assoc,
    add_comm (_ * _), add_assoc]
  simp only [EReal.coe_mul, EReal.coe_sub, EReal.coe_add,
    EReal.coe_ennreal_toReal (measure_ne_top _ _)]

lemma fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : β < γ) :
    fDiv (statInfoFun β γ) μ ν = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      + β * (μ.singularPart ν) univ + β * μ univ - γ * ν univ) := by
  have h_eq :
      (β : EReal) * ((μ.singularPart ν) univ)
        = ↑(2⁻¹ * (2 * β * ((μ.singularPart ν) univ).toReal)) := by
    simp [mul_assoc, EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  rw [fDiv_statInfoFun_eq_integral_max_of_nonneg_of_gt hβ hγ, integral_max_eq_integral_abs', h_eq,
    ← EReal.coe_add, ← mul_add, EReal.coe_mul]
  simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, sub_eq_add_neg,
    ← EReal.coe_neg, ← EReal.coe_add, add_assoc]
  congr 3
  ring

lemma fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      - β * (μ.singularPart ν) univ + γ * ν univ - β * μ univ) := by
  have h_eq :
      (β : EReal) * ((μ.singularPart ν) univ)
        = ↑(2⁻¹ * (2 * β * ((μ.singularPart ν) univ).toReal)) := by
    simp [mul_assoc, EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  rw [fDiv_statInfoFun_eq_integral_max_of_nonpos_of_le hβ hγ, integral_max_eq_integral_abs, h_eq,
    sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_add, ← mul_neg, ← mul_add, EReal.coe_mul]
  simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, sub_eq_add_neg,
    ← EReal.coe_neg, ← EReal.coe_add, add_assoc]
  congr 3
  ring

lemma fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : β < γ) :
    fDiv (statInfoFun β γ) μ ν = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      - β * (μ.singularPart ν) univ + β * μ univ - γ * ν univ) := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonpos_of_gt hβ hγ, integral_max_eq_integral_abs']
  simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, sub_eq_add_neg,
    ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_mul]
  ring_nf

lemma integral_statInfoFun_curvatureMeasure (hf_cvx : ConvexOn ℝ univ f)
    (hf_cont : Continuous f) (hf_one : f 1 = 0) (hfderiv_one : rightDeriv f 1 = 0) :
    ∫ y, statInfoFun 1 y t ∂(curvatureMeasure hf_cvx) = f t := by
  have h :
      f t - f 1 - (rightDeriv f 1) * (t - 1) = ∫ x in (1)..t, t - x ∂(curvatureMeasure hf_cvx) :=
    convex_taylor hf_cvx hf_cont
  rw [hf_one, hfderiv_one, sub_zero, zero_mul, sub_zero] at h
  rw [h]
  rcases le_total t 1 with (ht | ht)
  · simp_rw [statInfoFun_of_one_of_right_le_one ht, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_ge ht, ← integral_neg, neg_sub]
  · simp_rw [statInfoFun_of_one_of_one_le_right ht, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_le ht]

-- TODO: think about the case when the function is not integrable (`h_int`).
-- Can we prove that in this case the rhs is also not integrable?
lemma fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (hf_one : f 1 = 0)
    (hfderiv_one : rightDeriv f 1 = 0) (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ac : μ ≪ ν) :
    fDiv f μ ν = ∫ x, (fDiv (statInfoFun 1 x) μ ν).toReal ∂(curvatureMeasure hf_cvx) := by
  classical
  rw [fDiv_of_absolutelyContinuous h_ac, if_pos h_int, EReal.coe_eq_coe_iff]
  simp_rw [fDiv_of_absolutelyContinuous h_ac, if_pos (integrable_statInfoFun_rnDeriv 1 _ _ _),
    EReal.toReal_coe,
    ← integral_statInfoFun_curvatureMeasure hf_cvx hf_cont hf_one hfderiv_one]
  have h_meas : Measurable (fun x γ ↦ statInfoFun 1 γ ((∂μ/∂ν) x).toReal).uncurry := by
    change Measurable
      (statInfoFun.uncurry.uncurry ∘ (fun (xγ : 𝒳 × ℝ) ↦ ((1, xγ.2), ((∂μ/∂ν) xγ.1).toReal)))
    refine stronglymeasurable_statInfoFun.measurable.comp ?_
    refine (measurable_const.prod_mk measurable_snd).prod_mk ?_
    exact ((Measure.measurable_rnDeriv μ ν).comp measurable_fst).ennreal_toReal
  have int_eq_lint : ∫ x, ∫ γ, statInfoFun 1 γ ((∂μ/∂ν) x).toReal ∂curvatureMeasure hf_cvx ∂ν
      = (∫⁻ x, ∫⁻ γ, ENNReal.ofReal (statInfoFun 1 γ ((∂μ/∂ν) x).toReal)
        ∂curvatureMeasure hf_cvx ∂ν).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    rotate_left
    · exact eventually_of_forall fun _ ↦ (integral_nonneg (fun _ ↦ statInfoFun_nonneg _ _ _))
    · refine (StronglyMeasurable.integral_prod_left ?_).aestronglyMeasurable
      exact (measurable_swap_iff.mpr h_meas).stronglyMeasurable
    congr with x
    rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall fun y ↦ statInfoFun_nonneg _ _ _)
      h_meas.of_uncurry_left.stronglyMeasurable.aestronglyMeasurable]
    refine ENNReal.ofReal_toReal <| (lintegral_ofReal_le_lintegral_nnnorm _).trans_lt ?_ |>.ne
    exact (integrable_statInfoFun 1 _).hasFiniteIntegral
  rw [int_eq_lint, lintegral_lintegral_swap h_meas.ennreal_ofReal.aemeasurable,
    integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact eventually_of_forall fun _ ↦ (integral_nonneg (fun _ ↦ statInfoFun_nonneg _ _ _))
  · exact h_meas.stronglyMeasurable.integral_prod_left.aestronglyMeasurable
  congr with γ
  rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall fun _ ↦ statInfoFun_nonneg _ _ _)
    h_meas.of_uncurry_right.stronglyMeasurable.aestronglyMeasurable, ENNReal.ofReal_toReal]
  have h_lt_top := (integrable_statInfoFun_rnDeriv 1 γ μ ν).hasFiniteIntegral
  simp_rw [HasFiniteIntegral, lt_top_iff_ne_top] at h_lt_top
  convert h_lt_top
  rw [← ENNReal.toReal_eq_toReal ENNReal.ofReal_ne_top ENNReal.coe_ne_top, toReal_coe_nnnorm,
    ENNReal.toReal_ofReal (statInfoFun_nonneg _ _ _),
    Real.norm_of_nonneg (statInfoFun_nonneg _ _ _)]

end StatInfoFun

end ProbabilityTheory

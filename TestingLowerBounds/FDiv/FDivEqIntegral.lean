/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import TestingLowerBounds.Divergences.StatInfo.fDivStatInfo

/-!
# fDiv and StatInfo

-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞} {π : Measure Bool} {f : DivFunction} {β γ x t : ℝ}

section StatInfoFun

open Set Filter ConvexOn

lemma integrable_statInfoFun_one_curvatureMeasureReal_iff
    (hfderiv_one : rightDeriv f.realFun 1 = 0) {x : ℝ} (hx_nonneg : 0 ≤ x) :
    Integrable (fun γ ↦ statInfoFun 1 γ x) f.curvatureMeasureReal ↔ f (ENNReal.ofReal x) ≠ ∞ := by
  rcases le_total 1 x with hx | hx
  · rw [integrable_statInfoFun_one_iff_of_ge hx,
      f.integrable_curvatureMeasureReal_sub_iff_ne_top_of_ge hfderiv_one hx]
  · rw [integrable_statInfoFun_one_iff_of_le hx,
      f.integrable_curvatureMeasureReal_sub_iff_ne_top_of_le hfderiv_one hx_nonneg hx]

lemma integral_statInfoFun_curvatureMeasure' (hfderiv_one : rightDeriv f.realFun 1 = 0)
    (ht : 0 ≤ t) :
    ∫ y, statInfoFun 1 y t ∂f.curvatureMeasureReal = f.realFun t := by
  have : f.realFun t = ∫ x in (1)..t, t - x ∂f.curvatureMeasureReal :=
    f.convex_taylor_one hfderiv_one ht
  rcases le_total t 1 with (ht | ht)
  · simp_rw [this, statInfoFun_of_one_of_right_le_one ht, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_ge ht, ← integral_neg, neg_sub]
  · simp_rw [this, statInfoFun_of_one_of_one_le_right ht, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_le ht]

lemma integral_statInfoFun_curvatureMeasure'' (hfderiv_one : rightDeriv f.realFun 1 = 0)
    {t : ℝ≥0∞} (ht_ne : t ≠ ∞) (ht : f t ≠ ∞) :
    ENNReal.ofReal (∫ y, statInfoFun 1 y t.toReal ∂f.curvatureMeasureReal) = f t := by
  rw [← ENNReal.ofReal_toReal ht, ← f.realFun_toReal ht_ne,
    integral_statInfoFun_curvatureMeasure' hfderiv_one ENNReal.toReal_nonneg]

lemma lintegral_statInfoFun_curvatureMeasureReal (hfderiv_one : rightDeriv f.realFun 1 = 0)
    {t : ℝ≥0∞} (ht_ne : t ≠ ∞) :
    ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y t.toReal) ∂f.curvatureMeasureReal = f t := by
  by_cases ht : f t = ∞
  · rw [ht]
    by_contra h_ne
    have h_int : Integrable (fun y ↦ statInfoFun 1 y t.toReal) f.curvatureMeasureReal :=
      (lintegral_ofReal_ne_top_iff_integrable measurable_statInfoFun2.aestronglyMeasurable
        (ae_of_all _ fun x ↦ statInfoFun_nonneg _ _ _)).mp h_ne
    rw [integrable_statInfoFun_one_curvatureMeasureReal_iff hfderiv_one ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal ht_ne] at h_int
    exact h_int ht
  rw [← ofReal_integral_eq_lintegral_ofReal]
  rotate_left
  · rw [integrable_statInfoFun_one_curvatureMeasureReal_iff hfderiv_one ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal ht_ne]
    exact ht
  · exact ae_of_all _ fun x ↦ statInfoFun_nonneg _ _ _
  exact integral_statInfoFun_curvatureMeasure'' hfderiv_one ht_ne ht

lemma lintegral_statInfoFun_curvatureMeasure (hfderiv_one : rightDeriv f.realFun 1 = 0)
    {t : ℝ≥0∞} (ht_ne : t ≠ ∞) :
    ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y.toReal t.toReal) ∂f.curvatureMeasure = f t := by
  rw [← lintegral_statInfoFun_curvatureMeasureReal hfderiv_one ht_ne,
    f.lintegral_curvatureMeasureReal measurable_statInfoFun2.ennreal_ofReal]

lemma lintegral_f_rnDeriv_eq_lintegralfDiv_statInfoFun_of_absolutelyContinuous
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hfderiv_one : rightDeriv f.realFun 1 = 0)
    (h_ac : μ ≪ ν) :
    ∫⁻ x, f ((∂μ/∂ν) x) ∂ν = ∫⁻ x, fDiv (statInfoDivFun 1 x.toReal) μ ν ∂f.curvatureMeasure := by
  have h_meas : Measurable (fun x γ ↦ statInfoFun 1 γ ((∂μ/∂ν) x).toReal).uncurry :=
    measurable_statInfoFun.comp <|
      (measurable_const.prodMk measurable_snd).prodMk <|
      ((μ.measurable_rnDeriv ν).comp measurable_fst).ennreal_toReal
  classical
  simp_rw [fDiv_statInfoFun_eq_lintegral_of_ac h_ac]
  have : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y ((∂μ/∂ν) x).toReal)
          ∂f.curvatureMeasureReal ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [μ.rnDeriv_ne_top ν] with x hx_ne
    rw [lintegral_statInfoFun_curvatureMeasureReal hfderiv_one hx_ne]
  rw [this, lintegral_lintegral_swap, DivFunction.lintegral_curvatureMeasureReal]
  · exact Measurable.lintegral_prod_left h_meas.ennreal_ofReal
  · exact h_meas.ennreal_ofReal.aemeasurable

lemma fDiv_ne_top_iff_lintegral_fDiv_statInfoFun_ne_top_of_ac'
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfderiv_one : rightDeriv f.realFun 1 = 0) (h_ac : μ ≪ ν) :
    fDiv f μ ν ≠ ∞ ↔ ∫⁻ x, fDiv (statInfoDivFun 1 x.toReal) μ ν ∂f.curvatureMeasure ≠ ∞ := by
  rw [fDiv_ne_top_iff]
  simp only [h_ac, implies_true, and_true]
  rw [lintegral_f_rnDeriv_eq_lintegralfDiv_statInfoFun_of_absolutelyContinuous hfderiv_one h_ac]

lemma measurable_fDiv_statInfoFun_right [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Measurable fun y ↦ fDiv (statInfoDivFun 1 y) μ ν := by
  change Measurable ((fun p : ℝ × ℝ ↦ fDiv (statInfoDivFun p.1 p.2) μ ν) ∘ (fun x ↦ (1, x)))
  exact (measurable_fDiv_statInfoFun _ _).comp measurable_prodMk_left

lemma lintegral_fDiv_statInfoDivFun_curvatureMeasureReal_ne_top_iff
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal ≠ ∞ ↔
    Integrable (fun x ↦ (fDiv (statInfoDivFun 1 x) μ ν).toReal) f.curvatureMeasureReal := by
  rw [integrable_toReal_iff]
  · exact measurable_fDiv_statInfoFun_right.aemeasurable
  · exact ae_of_all _ fun x ↦ fDiv_statInfoDivFun_ne_top

lemma fDiv_ne_top_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous'
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hfderiv_one : rightDeriv f.realFun 1 = 0)
    (h_ac : μ ≪ ν) :
    fDiv f μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ (fDiv (statInfoDivFun 1 x) μ ν).toReal) f.curvatureMeasureReal := by
  rw [fDiv_ne_top_iff_lintegral_fDiv_statInfoFun_ne_top_of_ac' hfderiv_one h_ac,
    ← f.lintegral_curvatureMeasureReal (g := fun y ↦ fDiv (statInfoDivFun 1 y) μ ν),
    lintegral_fDiv_statInfoDivFun_curvatureMeasureReal_ne_top_iff]
  exact measurable_fDiv_statInfoFun_right

lemma fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous'
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfderiv_one : rightDeriv f.realFun 1 = 0) (h_ac : μ ≪ ν) :
    fDiv f μ ν = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal := by
  classical
  rw [fDiv_of_absolutelyContinuous h_ac,
    lintegral_f_rnDeriv_eq_lintegralfDiv_statInfoFun_of_absolutelyContinuous hfderiv_one h_ac,
    f.lintegral_curvatureMeasureReal measurable_fDiv_statInfoFun_right]

lemma lintegral_statInfoFun_one_zero' (hfderiv_one : rightDeriv f.realFun 1 = 0) :
    ∫⁻ x, ENNReal.ofReal (statInfoFun 1 x 0) ∂f.curvatureMeasureReal = f 0 := by
  norm_cast
  have := f.convex_taylor_one_left hfderiv_one zero_le_one
  simp only [tsub_zero] at this
  rw [this, f.lintegral_curvatureMeasureReal measurable_statInfoFun2.ennreal_ofReal]
  rw [← lintegral_indicator measurableSet_Ioc _]
  refine lintegral_congr fun x ↦ ?_
  simp_rw [statInfoFun_one_zero_right, indicator_apply]
  by_cases hx_top : x = ∞
  · simp [hx_top]
  have h_iff: x ∈ Ioc 0 1 ↔ x.toReal ∈ Ioc 0 1 := by
    simp only [mem_Ioc, ← ENNReal.ofReal_lt_iff_lt_toReal le_rfl hx_top,
        ← ENNReal.toReal_one, ENNReal.toReal_le_toReal hx_top ENNReal.one_ne_top,
        ENNReal.ofReal_zero]
  by_cases hx_mem : x ∈ Ioc 0 1
  · have hx_mem' : x.toReal ∈ Ioc 0 1 := h_iff.mp hx_mem
    simp [hx_mem, hx_mem', hx_top]
  · have hx_mem' : x.toReal ∉ Ioc 0 1 := fun h ↦ hx_mem (h_iff.mpr h)
    simp [hx_mem, hx_mem']

lemma lintegral_statInfoDivFun_one_zero' (hfderiv_one : rightDeriv f.realFun 1 = 0) :
    ∫⁻ x, statInfoDivFun 1 x 0 ∂f.curvatureMeasureReal = f 0 := by
  simp_rw [statInfoDivFun,
    DivFunction.ofReal_apply_zero_of_continuousWithinAt continuousWithinAt_statInfoFun_zero]
  exact lintegral_statInfoFun_one_zero' hfderiv_one

lemma measurable_derivAtTop_statInfoDivFun :
    Measurable fun x : ℝ ↦ (statInfoDivFun 1 x).derivAtTop := by
  simp_rw [derivAtTop_statInfoDivFun_eq]
  simp only [zero_le_one, ↓reduceIte, ENNReal.ofReal_one]
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

lemma lintegral_derivAtTop_statInfoDivFun_eq_toENNReal :
    ∫⁻ x, (statInfoDivFun 1 x).derivAtTop ∂f.curvatureMeasureReal
      = ((f.derivAtTop : EReal) - f.rightDerivStieltjes 1).toENNReal := by
  simp_rw [derivAtTop_statInfoDivFun_eq]
  simp only [zero_le_one, ↓reduceIte, ENNReal.ofReal_one]
  have : (fun x : ℝ ↦ if x ≤ 1 then (0 : ℝ≥0∞) else 1) = (Ioi 1).indicator 1 := by
    ext x
    split_ifs with h
    · simp [h]
    · simp [not_le.mp h]
  simp_rw [this, lintegral_indicator_one measurableSet_Ioi]
  rw [f.curvatureMeasureReal_apply measurableSet_Ioi]
  have : ENNReal.toReal ⁻¹' Ioi 1 = Ioo 1 ∞ := by
    ext x
    simp only [mem_preimage, mem_Ioi, mem_Ioo]
    constructor <;> intro h
    · by_cases hx_top : x = ∞
      · simp only [hx_top, ENNReal.toReal_top] at h
        exact absurd h (not_lt.mpr zero_le_one)
      · rw [← ENNReal.toReal_one, ENNReal.toReal_lt_toReal ENNReal.one_ne_top hx_top] at h
        exact ⟨h, Ne.lt_top hx_top⟩
    · rw [← ENNReal.toReal_one, ENNReal.toReal_lt_toReal ENNReal.one_ne_top h.2.ne]
      exact h.1
  rw [this]
  simp only [ne_eq, ENNReal.one_ne_top, not_false_eq_true,
    DivFunction.curvatureMeasure_Ioo_top_eq_curvatureMeasure_Ioi, f.curvatureMeasure_Ioi,
    ENNReal.toReal_one]
  rw [ERealStieltjes.measure_Ioi f.rightDerivStieltjes f.tendsto_rightDerivStieltjes_atTop]

lemma lintegral_derivAtTop_statInfoDivFun' (hfderiv_one : rightDeriv f.realFun 1 = 0) :
    ∫⁻ x, (statInfoDivFun 1 x).derivAtTop ∂f.curvatureMeasureReal = f.derivAtTop := by
  rw [lintegral_derivAtTop_statInfoDivFun_eq_toENNReal, DivFunction.rightDerivStieltjes_one,
    hfderiv_one]
  simp

/-- General form of `lintegral_derivAtTop_statInfoDivFun'`: without the assumption
`rightDeriv f.realFun 1 = 0`, the integral of the `derivAtTop` of the `statInfoDivFun`
misses the right derivative of `f` at `1`. -/
lemma lintegral_derivAtTop_statInfoDivFun :
    ∫⁻ x, (statInfoDivFun 1 x).derivAtTop ∂f.curvatureMeasureReal
      + ENNReal.ofReal (rightDeriv f.realFun 1) = f.derivAtTop := by
  rw [lintegral_derivAtTop_statInfoDivFun_eq_toENNReal, DivFunction.rightDerivStieltjes_one]
  by_cases h_top : f.derivAtTop = ∞
  · rw [h_top, EReal.coe_ennreal_top, EReal.top_sub_coe, EReal.toENNReal_top, top_add]
  · have h_le : rightDeriv f.realFun 1 ≤ f.derivAtTop.toReal :=
      f.rightDeriv_realFun_le_toReal_derivAtTop h_top (by simpa using DivFunction.xmin_lt_one)
        (by simpa using DivFunction.one_lt_xmax)
    rw [← EReal.coe_ennreal_toReal h_top, ← EReal.coe_sub,
      EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe,
      ← ENNReal.ofReal_add (sub_nonneg.mpr h_le) f.rightDeriv_one_nonneg, sub_add_cancel,
      ENNReal.ofReal_toReal h_top]

lemma fDiv_eq_lintegral_fDiv_statInfoFun' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfderiv_one : rightDeriv f.realFun 1 = 0) :
    fDiv f μ ν = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal := by
  rw [fDiv_eq_add_withDensity_derivAtTop,
    fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous' hfderiv_one
      (withDensity_absolutelyContinuous _ _),
    ← lintegral_derivAtTop_statInfoDivFun' hfderiv_one,
    ← lintegral_mul_const _ measurable_derivAtTop_statInfoDivFun,
    ← lintegral_add_right _ (measurable_derivAtTop_statInfoDivFun.mul_const _)]
  simp_rw [← fDiv_eq_add_withDensity_derivAtTop]

/-! ### The integral representation of `fDiv` without the assumption `rightDeriv f.realFun 1 = 0`

For a general `DivFunction`, the Taylor formula at `1` carries a linear term
`rightDeriv f.realFun 1 * (x - 1)`, hence the identity
`fDiv f μ ν = ∫ fDiv (statInfoDivFun 1 x) μ ν` only holds up to the term
`rightDeriv f.realFun 1 * (μ univ - ν univ)`, which we move to the appropriate side to stay in
`ℝ≥0∞`. -/

lemma lintegral_statInfoFun_curvatureMeasureReal_add {t : ℝ≥0∞} (ht_ne : t ≠ ∞) :
    ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y t.toReal) ∂f.curvatureMeasureReal
      + ENNReal.ofReal (rightDeriv f.realFun 1) * t
      = f t + ENNReal.ofReal (rightDeriv f.realFun 1) := by
  rcases le_total 1 t with ht | ht
  · have ht' : 1 ≤ t.toReal := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ht_ne ht
    have h_int : ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y t.toReal) ∂f.curvatureMeasureReal
        = ∫⁻ x in Ioc 1 t, t - x ∂f.curvatureMeasure := by
      simp_rw [statInfoFun_of_one_of_one_le_right ht']
      have : ∀ y, ENNReal.ofReal ((Ioc 1 t.toReal).indicator (fun y ↦ t.toReal - y) y)
          = (Ioc 1 t.toReal).indicator (fun y ↦ ENNReal.ofReal (t.toReal - y)) y := fun y ↦ by
        by_cases hy : y ∈ Ioc 1 t.toReal <;> simp [hy]
      simp_rw [this]
      rw [lintegral_indicator measurableSet_Ioc,
        f.setLIntegral_Ioc_curvatureMeasureReal (by fun_prop) zero_le_one, ENNReal.ofReal_one,
        ENNReal.ofReal_toReal ht_ne]
      refine setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ht_ne,
        ENNReal.ofReal_toReal (ne_top_of_le_ne_top ht_ne hx.2)]
    rw [h_int, f.convex_taylor_one_right' ht ht_ne]
    have : ENNReal.ofReal (rightDeriv f.realFun 1) * t
        = ENNReal.ofReal (rightDeriv f.realFun 1) * (t - 1)
          + ENNReal.ofReal (rightDeriv f.realFun 1) := by
      conv_lhs => rw [← tsub_add_cancel_of_le ht, mul_add, mul_one]
    rw [this]
    ring
  · have ht' : t.toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ENNReal.one_ne_top ht
    have h_int : ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y t.toReal) ∂f.curvatureMeasureReal
        = ∫⁻ x in Ioc t 1, x - t ∂f.curvatureMeasure := by
      simp_rw [statInfoFun_of_one_of_right_le_one ht']
      have : ∀ y, ENNReal.ofReal ((Ioc t.toReal 1).indicator (fun y ↦ y - t.toReal) y)
          = (Ioc t.toReal 1).indicator (fun y ↦ ENNReal.ofReal (y - t.toReal)) y := fun y ↦ by
        by_cases hy : y ∈ Ioc t.toReal 1 <;> simp [hy]
      simp_rw [this]
      rw [lintegral_indicator measurableSet_Ioc,
        f.setLIntegral_Ioc_curvatureMeasureReal (by fun_prop) ENNReal.toReal_nonneg,
        ENNReal.ofReal_one, ENNReal.ofReal_toReal ht_ne]
      refine setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ht_ne,
        ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hx.2)]
    rw [h_int, ← f.convex_taylor_one_left' ht, add_assoc, ← mul_add, tsub_add_cancel_of_le ht,
      mul_one]

lemma lintegral_f_rnDeriv_add_eq_lintegral_fDiv_statInfoFun_add_of_absolutelyContinuous
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
    ∫⁻ x, f ((∂μ/∂ν) x) ∂ν + ENNReal.ofReal (rightDeriv f.realFun 1) * ν univ
      = ∫⁻ x, fDiv (statInfoDivFun 1 x.toReal) μ ν ∂f.curvatureMeasure
        + ENNReal.ofReal (rightDeriv f.realFun 1) * μ univ := by
  have h_meas : Measurable (fun x γ ↦ statInfoFun 1 γ ((∂μ/∂ν) x).toReal).uncurry :=
    measurable_statInfoFun.comp <|
      (measurable_const.prodMk measurable_snd).prodMk <|
      ((μ.measurable_rnDeriv ν).comp measurable_fst).ennreal_toReal
  simp_rw [fDiv_statInfoFun_eq_lintegral_of_ac h_ac]
  have : ∫⁻ x, f ((∂μ/∂ν) x) ∂ν + ENNReal.ofReal (rightDeriv f.realFun 1) * ν univ
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y ((∂μ/∂ν) x).toReal)
          ∂f.curvatureMeasureReal ∂ν + ENNReal.ofReal (rightDeriv f.realFun 1) * μ univ := by
    rw [← lintegral_const, ← lintegral_add_right _ measurable_const]
    have h_eq : ∀ᵐ x ∂ν, f ((∂μ/∂ν) x) + ENNReal.ofReal (rightDeriv f.realFun 1)
        = ∫⁻ y, ENNReal.ofReal (statInfoFun 1 y ((∂μ/∂ν) x).toReal) ∂f.curvatureMeasureReal
          + ENNReal.ofReal (rightDeriv f.realFun 1) * (∂μ/∂ν) x := by
      filter_upwards [μ.rnDeriv_ne_top ν] with x hx
      rw [lintegral_statInfoFun_curvatureMeasureReal_add hx]
    rw [lintegral_congr_ae h_eq,
      lintegral_add_left (Measurable.lintegral_prod_right h_meas.ennreal_ofReal),
      lintegral_const_mul _ (μ.measurable_rnDeriv ν), Measure.lintegral_rnDeriv h_ac]
  rw [this, lintegral_lintegral_swap h_meas.ennreal_ofReal.aemeasurable,
    DivFunction.lintegral_curvatureMeasureReal]
  exact Measurable.lintegral_prod_left h_meas.ennreal_ofReal

/-- Integral representation of `fDiv f μ ν` in terms of the f-divergences of the
`statInfoDivFun 1 x` and the curvature measure of `f`. Compared to
`fDiv_eq_lintegral_fDiv_statInfoFun'`, no assumption is made on the right derivative of `f` at `1`,
at the price of the correction term `rightDeriv f.realFun 1 * (μ univ - ν univ)`, split here on
both sides of the equality to stay in `ℝ≥0∞`. -/
theorem fDiv_eq_lintegral_fDiv_statInfoFun [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ ν + ENNReal.ofReal (rightDeriv f.realFun 1) * ν univ
      = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal
        + ENNReal.ofReal (rightDeriv f.realFun 1) * μ univ := by
  have h_ac : ν.withDensity (∂μ/∂ν) ≪ ν := withDensity_absolutelyContinuous _ _
  have hμ : μ univ = ν.withDensity (∂μ/∂ν) univ + μ.singularPart ν univ := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
    rw [Measure.add_apply, add_comm]
  have h_in : ∀ x, fDiv (statInfoDivFun 1 x) μ ν
      = fDiv (statInfoDivFun 1 x) (ν.withDensity (∂μ/∂ν)) ν
        + (statInfoDivFun 1 x).derivAtTop * μ.singularPart ν univ :=
    fun x ↦ fDiv_eq_add_withDensity_derivAtTop μ ν
  simp_rw [h_in]
  rw [fDiv_eq_add_withDensity_derivAtTop,
    lintegral_add_right _ (measurable_derivAtTop_statInfoDivFun.mul_const _),
    lintegral_mul_const _ measurable_derivAtTop_statInfoDivFun,
    fDiv_of_absolutelyContinuous h_ac,
    f.lintegral_curvatureMeasureReal measurable_fDiv_statInfoFun_right,
    ← lintegral_derivAtTop_statInfoDivFun, hμ]
  have h2 := lintegral_f_rnDeriv_add_eq_lintegral_fDiv_statInfoFun_add_of_absolutelyContinuous
    (f := f) h_ac
  calc ∫⁻ x, f ((∂ν.withDensity (∂μ/∂ν)/∂ν) x) ∂ν
        + (∫⁻ x, (statInfoDivFun 1 x).derivAtTop ∂f.curvatureMeasureReal
            + ENNReal.ofReal (rightDeriv f.realFun 1)) * μ.singularPart ν univ
        + ENNReal.ofReal (rightDeriv f.realFun 1) * ν univ
      = (∫⁻ x, f ((∂ν.withDensity (∂μ/∂ν)/∂ν) x) ∂ν
          + ENNReal.ofReal (rightDeriv f.realFun 1) * ν univ)
        + ((∫⁻ x, (statInfoDivFun 1 x).derivAtTop ∂f.curvatureMeasureReal)
            * μ.singularPart ν univ
          + ENNReal.ofReal (rightDeriv f.realFun 1) * μ.singularPart ν univ) := by ring
    _ = (∫⁻ x, fDiv (statInfoDivFun 1 x.toReal) (ν.withDensity (∂μ/∂ν)) ν ∂f.curvatureMeasure
          + ENNReal.ofReal (rightDeriv f.realFun 1) * ν.withDensity (∂μ/∂ν) univ)
        + ((∫⁻ x, (statInfoDivFun 1 x).derivAtTop ∂f.curvatureMeasureReal)
            * μ.singularPart ν univ
          + ENNReal.ofReal (rightDeriv f.realFun 1) * μ.singularPart ν univ) := by rw [h2]
    _ = _ := by ring

end StatInfoFun

end ProbabilityTheory

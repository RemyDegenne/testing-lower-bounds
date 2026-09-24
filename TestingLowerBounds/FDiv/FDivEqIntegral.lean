/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import TestingLowerBounds.Divergences.StatInfo.fDivStatInfo

/-!
# Integral representation of f-divergences

Every f-divergence is an integral of the f-divergences of the functions `statInfoDivFun 1 x`
(which are statistical informations), against the curvature measure of `f`.

## Main statements

* `fDiv_eq_lintegral_fDiv_statInfoFun`: `fDiv f μ ν + f'(1) ν(X) = ∫ fDiv (statInfoDivFun 1 x) μ ν
  ∂γ_f + f'(1) μ(X)`, where `f'(1)` is the right derivative of `f.realFun` at `1` and `γ_f` the
  curvature measure of `f`.
* `fDiv_eq_lintegral_fDiv_statInfoFun'`: the same, for `f` with `f'(1) = 0`.

-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞} {π : Measure Bool} {f : DivFunction} {β γ x t : ℝ}

section StatInfoFun

open Set Filter ConvexOn

lemma measurable_fDiv_statInfoFun_right [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Measurable fun y ↦ fDiv (statInfoDivFun 1 y) μ ν := by
  change Measurable ((fun p : ℝ × ℝ ↦ fDiv (statInfoDivFun p.1 p.2) μ ν) ∘ (fun x ↦ (1, x)))
  exact (measurable_fDiv_statInfoFun _ _).comp measurable_prodMk_left

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

/-- The integral of the `derivAtTop` of the `statInfoDivFun 1 x` against the curvature measure of
`f` is `f.derivAtTop`, up to the right derivative of `f` at `1`. -/
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
`statInfoDivFun 1 x` and the curvature measure of `f`. The Taylor formula at `1` carries a linear
term, hence the correction term `rightDeriv f.realFun 1 * (μ univ - ν univ)`, split here on both
sides of the equality to stay in `ℝ≥0∞`. See `fDiv_eq_lintegral_fDiv_statInfoFun'` for the case
`rightDeriv f.realFun 1 = 0`. -/
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

/-- Integral representation of `fDiv f μ ν` in terms of the f-divergences of the
`statInfoDivFun 1 x` and the curvature measure of `f`, for `f` with `rightDeriv f.realFun 1 = 0`. -/
lemma fDiv_eq_lintegral_fDiv_statInfoFun' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfderiv_one : rightDeriv f.realFun 1 = 0) :
    fDiv f μ ν = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal := by
  simpa [hfderiv_one] using fDiv_eq_lintegral_fDiv_statInfoFun (f := f) (μ := μ) (ν := ν)

end StatInfoFun

end ProbabilityTheory

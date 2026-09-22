/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.StatInfo.fDivStatInfo

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

-- lemma integral_statInfoFun_curvatureMeasure :
--     ∫ y, statInfoFun 1 y t ∂f.curvatureMeasureReal
--       = f.realFun t - (rightDeriv f.realFun 1) * (t - 1) := by
--   have : f t - (rightDeriv f 1) * (t - 1) = ∫ x in (1)..t, t - x ∂f.curvatureMeasureReal :=
--     f.convex_taylor_one
--   rcases le_total t 1 with (ht | ht)
--   · simp_rw [this, statInfoFun_of_one_of_right_le_one ht, integral_indicator measurableSet_Ioc,
--       intervalIntegral.integral_of_ge ht, ← integral_neg, neg_sub]
--   · simp_rw [this, statInfoFun_of_one_of_one_le_right ht, integral_indicator measurableSet_Ioc,
--       intervalIntegral.integral_of_le ht]

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
    refine lintegral_ofReal_eq_top_of_not_integrable_of_nonneg ?_ ?_ ?_
    · refine (Measurable.stronglyMeasurable ?_).aestronglyMeasurable
      exact measurable_statInfoFun2
    · rw [integrable_statInfoFun_one_curvatureMeasureReal_iff hfderiv_one ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal ht_ne, ne_eq, not_not]
      exact ht
    · exact ae_of_all _ fun x ↦ statInfoFun_nonneg _ _ _
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
  sorry

lemma lintegral_derivAtTop_statInfoDivFun' (hfderiv_one : rightDeriv f.realFun 1 = 0) :
    ∫⁻ x, (statInfoDivFun 1 x).derivAtTop ∂f.curvatureMeasureReal = f.derivAtTop := by
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
  have : f.rightDerivStieltjes 1 = 0 := by simp [hfderiv_one]
  simp [this]

lemma fDiv_eq_lintegral_fDiv_statInfoFun' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfderiv_one : rightDeriv f.realFun 1 = 0) :
    fDiv f μ ν = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal := by
  rw [fDiv_eq_add_withDensity_derivAtTop,
    fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous' hfderiv_one
      (withDensity_absolutelyContinuous _ _),
    ← lintegral_derivAtTop_statInfoDivFun' hfderiv_one, ← lintegral_mul_const,
    ← lintegral_add_right]
  · simp_rw [← fDiv_eq_add_withDensity_derivAtTop]
  · sorry
  · sorry

-- todo: this is false. Find the right statement.
lemma fDiv_eq_lintegral_fDiv_statInfoFun [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ ν = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal := by
  sorry













-- -- lemma fDiv_eq_lintegral_fDiv_statInfoFun_of_mutuallySingular'
-- --     [IsFiniteMeasure μ] [IsFiniteMeasure ν]
-- --     (hfderiv_one : rightDeriv f.realFun 1 = 0) (h_ms : μ ⟂ₘ ν) :
-- --     fDiv f μ ν = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal := by
-- --   simp_rw [fDiv_of_mutuallySingular h_ms]
-- --   rw [lintegral_add_left, lintegral_mul_const, lintegral_mul_const,
-- --     lintegral_derivAtTop_statInfoDivFun' hfderiv_one,
-- --     lintegral_statInfoDivFun_one_zero' hfderiv_one]
-- --   · sorry
-- --   · sorry
-- --   · sorry

-- lemma fDiv_ne_top_iff_lintegral_fDiv_statInfoFun_ne_top_of_ac
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
--     fDiv f μ ν ≠ ∞ ↔ ∫⁻ x, fDiv (statInfoDivFun 1 x.toReal) μ ν ∂f.curvatureMeasure ≠ ∞ := by
--   sorry
--   -- rw [fDiv_eq_fDiv_centeredFunction (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0)),
--   --   EReal.add_ne_top_iff_of_ne_bot_of_ne_top]
--   -- rotate_left
--   -- · exact EReal.add_top_iff_ne_bot.mp rfl
--   -- · exact Ne.symm (ne_of_beq_false rfl)
--   -- rw [EReal.add_ne_top_iff_of_ne_bot_of_ne_top]
--   --   <;> try {· simp [EReal.mul_ne_top, EReal.mul_ne_bot, measure_ne_top]}
--   -- simp_rw [sub_eq_add_neg, ← neg_mul, mul_add, ← add_assoc]
--   -- rw [fDiv_ne_top_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous' _ _ (by ring) _ h_ac,
--   --   curvatureMeasure_add_const, curvatureMeasure_add_linear, curvatureMeasure_add_const]
--   -- · exact (hf_cvx.add_const _).add (const_mul_id (-rightDeriv f 1)) |>.add_const _
--   -- · exact ((hf_cont.add continuous_const).add (continuous_mul_left _)).add continuous_const
--   -- · have hf_diff := differentiableWithinAt_Ioi'
--   --     (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0)) zero_lt_one
--   --   rw [rightDeriv_add_const_apply, rightDeriv_add_linear_apply, rightDeriv_add_const_apply hf_diff,
--   --     add_neg_cancel] <;> fun_prop

-- lemma fDiv_ne_top_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
--     fDiv f μ ν ≠ ⊤
--       ↔ Integrable (fun x ↦ (fDiv (statInfoDivFun 1 x) μ ν).toReal) f.curvatureMeasureReal := by
--   rw [← lintegral_fDiv_statInfoDivFun_curvatureMeasureReal_ne_top_iff,
--     fDiv_ne_top_iff_lintegral_fDiv_statInfoFun_ne_top_of_ac h_ac,
--     f.lintegral_curvatureMeasureReal measurable_fDiv_statInfoFun_right]

-- lemma integrable_f_rnDeriv_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
--     Integrable (fun x ↦ f.realFun ((∂μ/∂ν) x).toReal) ν
--       ↔ Integrable (fun x ↦ (fDiv (statInfoDivFun 1 x) μ ν).toReal) f.curvatureMeasureReal := by
--   rw [← fDiv_ne_top_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous h_ac]
--   simp [fDiv_ne_top_iff, h_ac]
--   sorry

-- lemma fDiv_eq_lintegral_fDiv_statInfoFun_of_absolutelyContinuous
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (h_ac : μ ≪ ν) :
--     fDiv f μ ν = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal
--       + ((rightDeriv f.realFun 1 : EReal) * (μ univ - ν univ)).toENNReal := by
--   sorry
--   -- rw [fDiv_eq_fDiv_centeredFunction (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0))]
--   -- congr
--   -- · rw [fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous'
--   --     _ (by continuity) (by simp) _ _ h_ac]
--   --   · simp_rw [mul_sub, sub_eq_add_neg, neg_add, neg_neg, ← neg_mul, ← add_assoc,
--   --       curvatureMeasure_add_const, curvatureMeasure_add_linear, curvatureMeasure_add_const]
--   --   · simp_rw [mul_sub, sub_eq_add_neg, neg_add, neg_neg, ← neg_mul]
--   --     exact (hf_cvx.add_const _).add ((ConvexOn.const_mul_id _).add (convexOn_const _ convex_univ))
--   --   · have hf_diff := differentiableWithinAt_Ioi'
--   --       (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0)) zero_lt_one
--   --     simp_rw [mul_sub, sub_eq_add_neg, neg_add, neg_neg, ← neg_mul, ← add_assoc]
--   --     rw [rightDeriv_add_const_apply, rightDeriv_add_linear_apply,
--   --       rightDeriv_add_const_apply hf_diff, add_neg_cancel]
--   --     <;> fun_prop
--   --   · exact (h_int.sub (integrable_const _)).sub
--   --       ((Measure.integrable_toReal_rnDeriv.sub (integrable_const 1)).const_mul _)
--   -- all_goals exact ENNReal.toReal_toEReal_of_ne_top (measure_ne_top _ _)

-- -- lemma fDiv_eq_lintegral_fDiv_statInfoFun_of_absolutelyContinuous [IsFiniteMeasure μ]
-- --     [IsFiniteMeasure ν] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (h_ac : μ ≪ ν) :
-- --     fDiv f μ ν = ∫⁻ x, (fDiv (statInfoFun 1 x) μ ν).toENNReal ∂(curvatureMeasure f)
-- --       + f 1 * ν univ + rightDeriv f 1 * (μ univ - ν univ) := by
-- --   by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
-- --   · rw [fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous hf_cvx hf_cont h_int h_ac,
-- --       integral_eq_lintegral_of_nonneg_ae]
-- --     rotate_left
-- --     · exact .of_forall <| fun _ ↦ EReal.toReal_nonneg fDiv_statInfoFun_nonneg
-- --     · exact (stronglyMeasurable_fDiv_statInfoFun μ ν).measurable.comp (f := fun x ↦ (1, x))
-- --         (by fun_prop) |>.ereal_toReal.aestronglyMeasurable
-- --     simp_rw [← EReal.toENNReal_of_ne_top fDiv_statInfoFun_ne_top]
-- --     rw [ENNReal.toReal_toEReal_of_ne_top]
-- --     rw [integrable_f_rnDeriv_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous hf_cvx
-- --       hf_cont h_ac] at h_int
-- --     refine (integrable_toReal_iff ?_ ?_).mp ?_
-- --     · exact (stronglyMeasurable_fDiv_statInfoFun μ ν).measurable.comp (f := fun x ↦ (1, x))
-- --         (by fun_prop) |>.ereal_toENNReal.aemeasurable
-- --     · exact .of_forall fun _ ↦ EReal.toENNReal_ne_top_iff.mpr fDiv_statInfoFun_ne_top
-- --     simp_rw [EReal.toReal_toENNReal fDiv_statInfoFun_nonneg, h_int]
-- --   · classical
-- --     rw [fDiv_of_absolutelyContinuous h_ac, ite_eq_right h_int]
-- --     convert (EReal.top_add_of_ne_bot ?_).symm
-- --     swap
-- --     · simp [sub_eq_add_neg, measure_ne_top, EReal.add_ne_top, EReal.add_ne_bot, EReal.mul_ne_bot]
-- --     convert EReal.top_add_of_ne_bot ?_
-- --     swap; · simp [measure_ne_top, EReal.mul_ne_bot]
-- --     simp_rw [EReal.coe_ennreal_eq_top_iff]
-- --     have h := integrable_f_rnDeriv_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous
-- --       hf_cvx hf_cont h_ac |>.mpr.mt h_int
-- --     contrapose! h
-- --     simp_rw [← EReal.toReal_toENNReal fDiv_statInfoFun_nonneg]
-- --     refine (integrable_toReal_iff ?_ ?_).mpr h
-- --     · exact (stronglyMeasurable_fDiv_statInfoFun μ ν).measurable.comp (f := fun x ↦ (1, x))
-- --         (by fun_prop) |>.ereal_toENNReal.aemeasurable
-- --     · exact .of_forall fun _ ↦ EReal.toENNReal_ne_top_iff.mpr fDiv_statInfoFun_ne_top

-- lemma lintegral_statInfoFun_one_zero :
--     ∫⁻ x, ENNReal.ofReal (statInfoFun 1 x 0) ∂f.curvatureMeasureReal
--       = f 0 + ENNReal.ofReal (rightDeriv f.realFun 1) := by
--   norm_cast
--   have := convex_taylor hf_cvx hf_cont (a := 1) (b := 0)
--   simp only [zero_sub, mul_neg, mul_one, sub_neg_eq_add] at this
--   rw [this, intervalIntegral.integral_of_ge (zero_le_one' _), integral_neg, neg_neg,
--     ← ofReal_integral_eq_lintegral_ofReal _ (.of_forall fun x ↦ statInfoFun_nonneg 1 x 0)]
--   rotate_left
--   · refine Integrable.mono' (g := (Ioc 0 1).indicator 1) ?_
--       measurable_statInfoFun2.aestronglyMeasurable ?_
--     · exact IntegrableOn.integrable_indicator
--         (integrableOn_const.mpr (Or.inr measure_Ioc_lt_top)) measurableSet_Ioc
--     · simp_rw [Real.norm_of_nonneg (statInfoFun_nonneg 1 _ 0),
--         statInfoFun_of_one_of_right_le_one zero_le_one, sub_zero]
--       exact .of_forall fun x ↦ Set.indicator_le_indicator' fun hx ↦ hx.2
--   rw [EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg_of_ae <| .of_forall
--     fun x ↦ statInfoFun_nonneg 1 x 0), ← integral_indicator measurableSet_Ioc]
--   simp_rw [statInfoFun_of_one_of_right_le_one zero_le_one, sub_zero]

-- lemma fDiv_eq_lintegral_fDiv_statInfoFun_of_mutuallySingular [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (h_ms : μ ⟂ₘ ν) :
--     fDiv f μ ν = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal
--       + ((rightDeriv f.realFun 1 : EReal) * (μ univ - ν univ)).toENNReal := by
--   have hf_cvx' : ConvexOn ℝ (Ici 0) f := (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0))
--   have h1 : ∫⁻ x, (statInfoFun 1 x 0 * (ν univ).toEReal
--         + derivAtTop (statInfoFun 1 x) * μ univ).toENNReal ∂curvatureMeasure f
--       = (∫⁻ x, ENNReal.ofReal (statInfoFun 1 x 0) ∂curvatureMeasure f) * ν univ
--         + (∫⁻ x, (derivAtTop (statInfoFun 1 x)).toENNReal ∂curvatureMeasure f) * μ univ := by
--     rw [← lintegral_mul_const _ (Measurable.ennreal_ofReal measurable_statInfoFun2),
--       ← lintegral_mul_const _]
--     swap
--     · simp_rw [derivAtTop_statInfoFun_eq]
--       refine (Measurable.ite (.const _) ?_ ?_).coe_real_ereal.ereal_toENNReal <;>
--       · refine Measurable.ite (measurableSet_le (fun _ a ↦ a) ?_) ?_ ?_ <;> exact measurable_const
--     rw [← lintegral_add_left]
--     swap; · exact measurable_statInfoFun2.ennreal_ofReal.mul_const _
--     congr with x
--     rw [EReal.toENNReal_add]
--     rotate_left
--     · exact mul_nonneg (EReal.coe_nonneg.mpr (statInfoFun_nonneg 1 x 0))
--         (EReal.coe_ennreal_nonneg _)
--     · exact mul_nonneg (derivAtTop_statInfoFun_nonneg 1 x) (EReal.coe_ennreal_nonneg _)
--     rw [EReal.toENNReal_mul (EReal.coe_nonneg.mpr <| statInfoFun_nonneg 1 x 0),
--       EReal.toENNReal_mul (derivAtTop_statInfoFun_nonneg 1 x)]
--     simp [-statInfoFun_of_one]
--   have h2 : ∫⁻ x, (derivAtTop (statInfoFun 1 x)).toENNReal ∂curvatureMeasure f
--       = (derivAtTop f - rightDeriv f 1).toENNReal := by
--     calc
--       _ = curvatureMeasure f (Ioi 1) := by
--         simp_rw [derivAtTop_statInfoFun_eq, ← lintegral_indicator_one measurableSet_Ioi]
--         congr with x
--         by_cases h : x ∈ Ioi 1
--         · simpa [h]
--         · simp [h, show x ≤ 1 from le_of_not_lt h]
--       _ = (derivAtTop f - rightDeriv f 1).toENNReal := by
--         rw [curvatureMeasure_of_convexOn hf_cvx]
--         by_cases h_top : derivAtTop f = ⊤
--         · rw [h_top, EReal.top_sub_coe, EReal.toENNReal_top,
--             StieltjesFunction.measure_Ioi_of_tendsto_atTop_atTop]
--           exact hf_cvx'.derivAtTop_eq_top_iff.mp h_top
--         · lift (derivAtTop f) to ℝ using ⟨h_top, hf_cvx'.derivAtTop_ne_bot⟩ with x hx
--           rw [StieltjesFunction.measure_Ioi _ ?_ 1 (l := x)]
--           · norm_cast
--           exact (hx ▸ hf_cvx'.tendsto_toReal_derivAtTop (hx ▸ h_top) :)
--   simp_rw [fDiv_of_mutuallySingular h_ms, h1]
--   push_cast
--   rw [lintegral_statInfoFun_one_zero hf_cvx hf_cont, h2, EReal.coe_toENNReal]
--   swap
--   · rw [EReal.sub_nonneg (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
--     exact rightDeriv_le_derivAtTop hf_cvx' zero_lt_one
--   simp_rw [sub_eq_add_neg, ← ENNReal.toReal_toEReal_of_ne_top (measure_ne_top ν _),
--     ← ENNReal.toReal_toEReal_of_ne_top (measure_ne_top μ _),
--     EReal.add_mul_coe_of_nonneg ENNReal.toReal_nonneg, ← EReal.coe_neg (ν univ).toReal,
--     ← EReal.coe_add, ← EReal.coe_mul _ (_ + _), mul_add, EReal.coe_add, neg_mul, ← EReal.coe_mul,
--     mul_neg, EReal.coe_neg, add_assoc]
--   congr
--   simp_rw [add_comm (rightDeriv f 1 * (ν _).toReal).toEReal, add_assoc,
--     add_comm _ (rightDeriv f 1 * _).toEReal, ← add_assoc, ← sub_eq_add_neg,
--     EReal.add_sub_cancel_right, sub_eq_add_neg, add_assoc, add_comm _ (_ + (_ + (_ + _))),
--     add_comm (f 1 * _).toEReal, ← add_assoc, ← sub_eq_add_neg, EReal.add_sub_cancel_right,
--     sub_eq_add_neg, add_assoc, add_comm (-(rightDeriv f 1 * _).toEReal), ← add_assoc,
--     ← sub_eq_add_neg, EReal.add_sub_cancel_right]

-- lemma fDiv_eq_lintegral_fDiv_statInfoFun [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     fDiv f μ ν = ∫⁻ x, fDiv (statInfoDivFun 1 x) μ ν ∂f.curvatureMeasureReal
--       + ((rightDeriv f.realFun 1 : EReal) * (μ univ - ν univ)).toENNReal := by
--   rw [fDiv_eq_add_withDensity_singularPart _ _ (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0)),
--     fDiv_eq_lintegral_fDiv_statInfoFun_of_mutuallySingular hf_cvx hf_cont
--     (μ.mutuallySingular_singularPart ν), fDiv_eq_lintegral_fDiv_statInfoFun_of_absolutelyContinuous
--     hf_cvx hf_cont (withDensity_absolutelyContinuous ν (∂μ/∂ν))]
--   have h1 : ∫⁻ x, (fDiv (statInfoFun 1 x) μ ν).toENNReal ∂curvatureMeasure f
--       = ∫⁻ x, (fDiv (statInfoFun 1 x) (ν.withDensity (∂μ/∂ν)) ν).toENNReal ∂curvatureMeasure f
--         + ∫⁻ x, (fDiv (statInfoFun 1 x) (μ.singularPart ν) ν).toENNReal ∂curvatureMeasure f
--         - (∫⁻ x, .ofReal (statInfoFun 1 x 0) ∂curvatureMeasure f : EReal) * (ν univ).toReal := by
--     have h_nonneg (x : ℝ) : 0 ≤ fDiv (statInfoFun 1 x) μ ν := fDiv_statInfoFun_nonneg
--     simp_rw [fDiv_eq_add_withDensity_singularPart μ ν ((convexOn_statInfoFun 1 _).subset
--       (fun _ _ ↦ trivial) (convex_Ici 0))] at h_nonneg ⊢
--     rw_mod_cast [← lintegral_add_left]
--     swap; · exact ((stronglyMeasurable_fDiv_statInfoFun (ν.withDensity (∂μ/∂ν)) ν).measurable.comp
--       (by fun_prop) (f := fun x ↦ (1, x))).ereal_toENNReal
--     simp_rw [← EReal.toENNReal_add fDiv_statInfoFun_nonneg fDiv_statInfoFun_nonneg]
--     have h_ne_top : (∫⁻ x, .ofReal (statInfoFun 1 x 0) ∂curvatureMeasure f) * ν univ ≠ ⊤ := by
--       refine ENNReal.mul_ne_top (lt_top_iff_ne_top.mp ?_) (measure_ne_top ν _)
--       calc
--         _ ≤ ∫⁻ x, (Ioc 0 1).indicator 1 x ∂curvatureMeasure f := by
--           simp_rw [statInfoFun_of_one_of_right_le_one zero_le_one, sub_zero]
--           refine lintegral_mono (le_indicator ?_ ?_) <;> simp_all
--         _ < _ := by
--           rw [lintegral_indicator_one measurableSet_Ioc]
--           exact measure_Ioc_lt_top
--     have h_le (x : ℝ) : .ofReal (statInfoFun 1 x 0) * ν univ
--         ≤ (fDiv (statInfoFun 1 x) (ν.withDensity (∂μ/∂ν)) ν
--           + fDiv (statInfoFun 1 x) (μ.singularPart ν) ν).toENNReal := by
--       rw [← EReal.real_coe_toENNReal, ← EReal.toENNReal_coe (x := ν _),
--         ← EReal.toENNReal_mul (EReal.coe_nonneg.mpr <| statInfoFun_nonneg 1 x 0)]
--       refine EReal.toENNReal_le_toENNReal <| (EReal.sub_nonneg ?_ ?_).mp (h_nonneg x)
--         <;> simp [EReal.mul_ne_top, EReal.mul_ne_bot, measure_ne_top ν univ]
--     rw [ENNReal.toReal_toEReal_of_ne_top (measure_ne_top ν _), ← EReal.coe_ennreal_mul,
--       ← ENNReal.toEReal_sub h_ne_top]
--     swap
--     · exact lintegral_mul_const' _ _ (measure_ne_top ν _) ▸ lintegral_mono h_le
--     rw [← lintegral_mul_const' _ _ (measure_ne_top ν _),
--       ← lintegral_sub (measurable_statInfoFun2.ennreal_ofReal.mul_const _)
--       (lintegral_mul_const' _ _ (measure_ne_top ν _) ▸ h_ne_top) (.of_forall h_le)]
--     congr with x
--     rw [EReal.toENNReal_sub (mul_nonneg (EReal.coe_nonneg.mpr (statInfoFun_nonneg 1 x 0))
--       (EReal.coe_ennreal_nonneg _)),
--       EReal.toENNReal_mul (EReal.coe_nonneg.mpr (statInfoFun_nonneg 1 x 0)), EReal.toENNReal_coe]
--     congr
--   simp_rw [h1, lintegral_statInfoFun_one_zero hf_cvx hf_cont, sub_eq_add_neg, add_assoc]
--   congr 1
--   simp_rw [add_comm (- (((f 0).toEReal + _) * _)), add_comm (∫⁻ _, _ ∂_).toEReal _, ← add_assoc,
--     ← ENNReal.toReal_toEReal_of_ne_top (measure_ne_top _ _)]
--   norm_cast
--   ring_nf
--   simp_rw [sub_eq_add_neg, mul_assoc, ← mul_neg, ← mul_add]
--   congr 1
--   nth_rw 3 [μ.haveLebesgueDecomposition_add ν]
--   rw [Measure.coe_add, Pi.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
--   ring_nf

end StatInfoFun

end ProbabilityTheory

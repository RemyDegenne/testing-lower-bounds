/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.KullbackLeibler.KullbackLeibler
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Hellinger divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details

-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

--TODO: try to add these attributes to fun_prop? how to do this?
attribute [fun_prop] Measure.measurable_rnDeriv Measurable.ennreal_toReal
variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

-- todo: rename and move.
lemma integral_rpow_rnDeriv (ha_pos : 0 < a) (ha : a ≠ 1) [SigmaFinite μ] [SigmaFinite ν] :
    ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν = ∫ x, ((∂ν/∂μ) x).toReal ^ (1 - a) ∂μ := by
  let p := ∂μ/∂(μ + ν)
  let q := ∂ν/∂(μ + ν)
  calc ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν
    = ∫ x, ((p/q) x).toReal ^ a ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [μ.rnDeriv_eq_div ν] with x hx
        simp only [hx, Pi.div_apply, p, q]
  _ = ∫ x, (q x).toReal * ((p/q) x).toReal ^ a ∂(μ + ν) := by
        rw [← integral_rnDeriv_smul (_ : ν ≪ μ + ν)]
        · simp
        · rw [add_comm]
          exact Measure.AbsolutelyContinuous.rfl.add_right μ
  _ = ∫ x, (p x).toReal * ((q/p) x).toReal ^ (1 - a) ∂(μ + ν) := by
        refine integral_congr_ae ?_
        filter_upwards [μ.rnDeriv_lt_top (μ + ν), ν.rnDeriv_lt_top (μ + ν)]
          with x hp_top hq_top
        by_cases hp : p x = 0
        · simp [hp, ha_pos.ne']
        by_cases hq : q x = 0
        · simp only [hq, ENNReal.zero_toReal, Pi.div_apply, zero_mul, ENNReal.zero_div,
            zero_eq_mul, le_refl]
          refine Or.inr ?_
          rw [zero_rpow]
          rwa [ne_eq, sub_eq_zero, Eq.comm]
        simp only [Pi.div_apply, ENNReal.toReal_div, div_eq_mul_inv, ENNReal.toReal_mul,
          mul_rpow ENNReal.toReal_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg), ENNReal.toReal_inv,
          inv_rpow ENNReal.toReal_nonneg, ← rpow_neg ENNReal.toReal_nonneg, neg_sub]
        rw [mul_comm, mul_assoc, mul_comm _ ((p x).toReal ^ (a - 1)), ← mul_assoc (p x).toReal]
        congr
        · have : a = 1 + (a - 1) := by abel
          conv_lhs => rw [this]
          rw [rpow_add, rpow_one]
          rw [ENNReal.toReal_pos_iff]
          exact ⟨zero_le'.lt_of_ne' hp, hp_top⟩
        · rw [mul_comm, rpow_sub, rpow_one, rpow_neg ENNReal.toReal_nonneg, div_eq_mul_inv]
          rw [ENNReal.toReal_pos_iff]
          exact ⟨zero_le'.lt_of_ne' hq, hq_top⟩
  _ = ∫ x, ((q/p) x).toReal ^ (1 - a) ∂μ := by
        rw [← integral_rnDeriv_smul (_ : μ ≪ μ + ν)]
        · simp
        · exact Measure.AbsolutelyContinuous.rfl.add_right ν
  _ = ∫ x, ((∂ν/∂μ) x).toReal ^ (1 - a) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [ν.rnDeriv_eq_div μ] with x hx
        rw [add_comm] at hx
        simp only [hx, Pi.div_apply, p, q]

lemma integrable_rpow_rnDeriv_iff [SigmaFinite ν] [SigmaFinite μ] (hμν : μ ≪ ν) (ha : 0 < a) :
    Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) μ
      ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ (1 + a)) ν := by
  rw [← integrable_rnDeriv_smul_iff hμν]
  refine integrable_congr ?_
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx
  simp only [smul_eq_mul]
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [h_zero, ENNReal.zero_toReal, zero_mul]
    rw [zero_rpow]
    linarith
  · rw [rpow_add (ENNReal.toReal_pos h_zero hx), rpow_one]

lemma integral_fun_rnDeriv_eq_zero_iff_mutuallySingular [SigmaFinite μ] [SigmaFinite ν]
    {f : ENNReal → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) (hf_zero : ∀ x, f x = 0 ↔ x = 0 ∨ x = ⊤)
    (h_int : Integrable (f ∘ (∂μ/∂ν)) ν) :
    ∫ x, f ((∂μ/∂ν) x) ∂ν = 0 ↔ μ ⟂ₘ ν := by
  rw [← Measure.rnDeriv_eq_zero, integral_eq_zero_iff_of_nonneg (fun _ ↦ hf_nonneg _) h_int]
  apply Filter.eventually_congr
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx
  simp only [Pi.zero_apply, hf_zero, hx, or_false]

lemma integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular [SigmaFinite μ] [SigmaFinite ν]
    (ha_zero : a ≠ 0) (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) :
    ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν = 0 ↔ μ ⟂ₘ ν := by
  have h_nonneg : ∀ (x : ENNReal), 0 ≤ x.toReal ^ a := by
    intro x
    simp only [Pi.zero_apply, ENNReal.toReal_nonneg, rpow_nonneg]
  refine integral_fun_rnDeriv_eq_zero_iff_mutuallySingular h_nonneg (fun x ↦ ?_) h_int
  rw [rpow_eq_zero ENNReal.toReal_nonneg ha_zero, ENNReal.toReal_eq_zero_iff]

lemma integral_rpow_rnDeriv_pos_iff_not_mutuallySingular [SigmaFinite μ] [SigmaFinite ν]
    (ha_zero : a ≠ 0) (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) :
    0 < ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν ↔ ¬ μ ⟂ₘ ν := by
  rw [← integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular ha_zero h_int]
  push_neg
  have h_nonneg : 0 ≤ ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν := by
    apply integral_nonneg
    intro x
    simp only [Pi.zero_apply, ENNReal.toReal_nonneg, rpow_nonneg]
  exact LE.le.gt_iff_ne h_nonneg

section HellingerFun

/--Hellinger function, defined as `x ↦ (a - 1)⁻¹ * (x ^ a - 1)` for `a ∈ (0, 1) ∪ (1, + ∞)`.
At `0` the function is obtained by contiuity and is the indicator function of `{0}`. At `1` it is
defined as `x ↦ x * log x`, because in this way we obtain that the Hellinger divergence at `1`
conincides with the KL divergence, which is natural for continuity reasons.-/
noncomputable
def hellingerFun (a : ℝ) : ℝ → ℝ :=
  if a = 0 then fun x ↦ if x = 0 then 1 else 0
  else if a = 1 then fun x ↦ x * log x
  else fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)

lemma hellingerFun_zero : hellingerFun 0 = fun x ↦ if x = 0 then 1 else 0 := by
  ext x
  simp [hellingerFun]

lemma hellingerFun_zero' : hellingerFun 0 = fun x ↦ 0 ^ x := by
  ext x
  by_cases h : x = 0 <;> simp [hellingerFun, h]

lemma hellingerFun_zero'' : hellingerFun 0 = Set.indicator {0} 1 := by
  ext x
  by_cases h : x = 0 <;> simp [hellingerFun_zero, h]

@[simp]
lemma hellingerFun_one : hellingerFun 1 = fun x ↦ x * log x := by
  ext x
  simp [hellingerFun]

lemma hellingerFun_of_ne_zero_of_ne_one (ha_zero : a ≠ 0) (ha_one : a ≠ 1) :
    hellingerFun a = fun x ↦ (a - 1)⁻¹ * (x ^ a - 1) := by
  ext x
  simp [hellingerFun, ha_zero, ha_one]

lemma continuous_rpow_const (ha_nonneg : 0 ≤ a) : Continuous fun (x : ℝ) ↦ x ^ a := by
  rw [continuous_iff_continuousAt]
  exact fun _ ↦ continuousAt_rpow_const _ _ (Or.inr ha_nonneg)

lemma continuous_hellingerFun (ha_pos : 0 < a) : Continuous (hellingerFun a) := by
  by_cases ha_eq : a = 1
  · rw [ha_eq, hellingerFun_one]
    simp [Real.continuous_mul_log]
  rw [hellingerFun, if_neg ha_pos.ne', if_neg ha_eq]
  exact continuous_const.mul ((continuous_rpow_const ha_pos.le).sub continuous_const)

lemma stronglyMeasurable_hellingerFun (ha_nonneg : 0 ≤ a) :
    StronglyMeasurable (hellingerFun a) := by
  cases  (lt_or_eq_of_le ha_nonneg) with
  | inl ha_pos => exact (continuous_hellingerFun ha_pos).stronglyMeasurable
  | inr ha_eq =>
    rw [← ha_eq, hellingerFun_zero'']
    measurability

@[simp]
lemma hellingerFun_apply_one_eq_zero : hellingerFun a 1 = 0 := by
  by_cases ha_one : a = 1
  · simp [ha_one, hellingerFun_one]
  by_cases ha_zero : a = 0
  · simp [ha_zero, hellingerFun_zero]
  simp [hellingerFun, ha_one, ha_zero]

lemma hellingerFun_apply_zero : hellingerFun a 0 = (1 - a)⁻¹ := by
  by_cases ha_zero : a = 0
  · simp [ha_zero, hellingerFun_zero]
  by_cases ha_one : a = 1
  · simp [ha_one, hellingerFun_one]
  simp [hellingerFun, ha_zero, ha_one, neg_inv]

lemma convexOn_hellingerFun (ha_pos : 0 ≤ a) : ConvexOn ℝ (Set.Ici 0) (hellingerFun a) := by
  by_cases ha_zero : a = 0
  · refine convexOn_iff_slope_mono_adjacent.mpr ?_
    simp only [convex_Ici, Set.mem_Ici, smul_eq_mul, true_and, hellingerFun_zero, ha_zero]
    intro x y z hx _ hxy hyz
    simp only [(lt_of_le_of_lt hx hxy).ne', ↓reduceIte, zero_sub,
      (gt_trans hyz <| lt_of_le_of_lt hx hxy).ne', sub_self, zero_div, div_nonpos_iff,
      Left.nonneg_neg_iff, tsub_le_iff_right, zero_add, Left.neg_nonpos_iff, sub_nonneg]
    exact Or.inr ⟨by positivity, by linarith⟩
  replace ha_pos := ha_pos.lt_of_ne fun h ↦ ha_zero h.symm
  rcases (lt_trichotomy a 1) with (ha | ha | ha)
  · have : hellingerFun a = - (fun x ↦ (1 - a)⁻¹ • (x ^ a - 1)) := by
      ext x
      rw [Pi.neg_apply, hellingerFun_of_ne_zero_of_ne_one ha_pos.ne' ha.ne, smul_eq_mul, ← neg_mul,
        neg_inv, neg_sub]
    rw [this]
    exact ((Real.concaveOn_rpow ha_pos.le ha.le).sub (convexOn_const _ (convex_Ici 0))).smul
      (by simp [ha.le]) |>.neg
  · simp only [hellingerFun, ha, one_ne_zero, ↓reduceIte]
    exact convexOn_mul_log
  · simp_rw [hellingerFun, ← smul_eq_mul, if_neg ha_pos.ne', if_neg ha.ne']
    exact (convexOn_rpow ha.le).sub (concaveOn_const _ (convex_Ici 0)) |>.smul (by simp [ha.le])

lemma hasDerivAt_hellingerFun (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (hellingerFun a)
      (if a = 0 then 0
      else if a = 1 then log x + 1
      else (a - 1)⁻¹ * a * x ^ (a - 1)) x := by
  split_ifs with h1 h2
  · rw [h1, hellingerFun_zero]
    refine HasDerivAt.congr_of_eventuallyEq (f := fun _ ↦ 0) (hasDerivAt_const _ _) ?_
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [hy]
  · simp only [h2, hellingerFun_one]
    exact Real.hasDerivAt_mul_log hx
  · rw [hellingerFun_of_ne_zero_of_ne_one h1 h2, mul_assoc]
    refine HasDerivAt.const_mul _ ?_
    exact (Real.hasDerivAt_rpow_const (Or.inl hx)).sub_const _

lemma rightDeriv_hellingerFun (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    rightDeriv (hellingerFun a) x =
      if a = 0 then 0
      else if a = 1 then log x + 1
      else (a - 1)⁻¹ * a * x ^ (a - 1) :=
  rightDeriv_of_hasDerivAt (hasDerivAt_hellingerFun a hx)

lemma tendsto_rightDeriv_hellingerFun_atTop_of_one_lt (ha : 1 < a) :
    Tendsto (rightDeriv (hellingerFun a)) atTop atTop := by
  have : rightDeriv (hellingerFun a) =ᶠ[atTop] fun x ↦ (a - 1)⁻¹ * a * x ^ (a - 1) := by
    filter_upwards [eventually_ne_atTop 0] with x hx
    rw [rightDeriv_hellingerFun _ hx]
    simp [(zero_lt_one.trans ha).ne', ha.ne']
  rw [tendsto_congr' this]
  simp_rw [mul_assoc, tendsto_const_mul_atTop_iff]
  have h1 : ¬ a < 0 := by linarith
  have h2 : ¬ a < 1 := by linarith
  simp only [inv_pos, sub_pos, ha, zero_lt_one.trans ha, true_and, h1, false_and, or_false,
    inv_neg'', sub_neg, h2]
  exact tendsto_rpow_atTop (by linarith)

lemma tendsto_rightDeriv_hellingerFun_atTop_of_lt_one (ha : a < 1) :
    Tendsto (rightDeriv (hellingerFun a)) atTop (𝓝 0) := by
  by_cases ha_zero : a = 0
  · rw [ha_zero]
    have : rightDeriv (hellingerFun 0) =ᶠ[atTop] fun _ ↦ 0 := by
      filter_upwards [eventually_ne_atTop 0] with x hx
      simp [rightDeriv_hellingerFun _ hx]
    rw [tendsto_congr' this]
    exact tendsto_const_nhds
  · have : rightDeriv (hellingerFun a) =ᶠ[atTop] fun x ↦ (a - 1)⁻¹ * a * x ^ (a - 1) := by
      filter_upwards [eventually_ne_atTop 0] with x hx
      rw [rightDeriv_hellingerFun _ hx]
      simp [ha_zero, ha.ne]
    rw [tendsto_congr' this]
    have h_zero : 0 = (a - 1)⁻¹ * a * 0 := by simp
    rw [h_zero]
    refine Tendsto.const_mul _ ?_
    have : (fun (x : ℝ) ↦ x ^ (a - 1)) = (fun x ↦ x ^ (-(1 - a))) := by ext x; simp
    rw [this]
    exact tendsto_rpow_neg_atTop (by linarith)

lemma derivAtTop_hellingerFun_of_one_lt (ha : 1 < a) : derivAtTop (hellingerFun a) = ⊤ :=
  derivAtTop_of_tendsto_atTop <| tendsto_rightDeriv_hellingerFun_atTop_of_one_lt ha

lemma derivAtTop_hellingerFun_of_one_le (ha : 1 ≤ a) :
    derivAtTop (hellingerFun a) = ⊤ := by
  by_cases ha_eq : a = 1
  · simp only [hellingerFun, ha, ha_eq, one_ne_zero, ↓reduceIte, derivAtTop_mul_log]
  · exact derivAtTop_hellingerFun_of_one_lt <| lt_of_le_of_ne ha fun h ↦ ha_eq h.symm

lemma derivAtTop_hellingerFun_of_lt_one (ha : a < 1) :
    derivAtTop (hellingerFun a) = 0 :=
  derivAtTop_of_tendsto_nhds <| tendsto_rightDeriv_hellingerFun_atTop_of_lt_one ha

lemma integrable_hellingerFun_iff_integrable_rpow (ha_one : a ≠ 1) [IsFiniteMeasure ν] :
    Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν := by
  by_cases ha_zero : a = 0
  · simp_rw [ha_zero, hellingerFun_zero'', rpow_zero, integrable_const, iff_true,
      ← Set.indicator_comp_right fun x ↦ ((∂μ/∂ν) x).toReal, Set.preimage, Set.mem_singleton_iff,
      Pi.one_comp]
    refine (integrable_indicator_iff ?_).mpr ?_
    · apply measurableSet_eq_fun <;> fun_prop
    · exact integrableOn_const.mpr (Or.inr (measure_lt_top ν _))
  rw [hellingerFun_of_ne_zero_of_ne_one ha_zero ha_one, integrable_const_mul_iff]
  swap; · simp [sub_eq_zero, ha_one]
  simp_rw [sub_eq_add_neg, integrable_add_const_iff]

lemma integrable_hellingerFun_zero [IsFiniteMeasure ν] :
    Integrable (fun x ↦ hellingerFun 0 ((∂μ/∂ν) x).toReal) ν := by
  simp_rw [integrable_hellingerFun_iff_integrable_rpow zero_ne_one, rpow_zero]
  exact integrable_const _

lemma integrable_hellingerFun_rnDeriv_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  refine integrable_f_rnDeriv_of_derivAtTop_ne_top μ ν ?_ ?_ ?_
  · exact stronglyMeasurable_hellingerFun ha_nonneg
  · exact convexOn_hellingerFun ha_nonneg
  · rw [derivAtTop_hellingerFun_of_lt_one ha]
    exact EReal.zero_ne_top

lemma integrable_rpow_rnDeriv_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν := by
  rw [← integrable_hellingerFun_iff_integrable_rpow ha.ne]
  exact integrable_hellingerFun_rnDeriv_of_lt_one ha_nonneg ha

end HellingerFun

/-- Hellinger divergence of order `a`.
The cases `a = 0` and `a = 1` are defined separately inside the definition of the Hellinger
function, so that in the case `a = 0` we have `hellingerDiv 0 μ ν = ν {x | (∂μ/∂ν) x = 0}`, and in
the case `a = 1` the Hellinger divergence coincides with the KL divergence. -/
noncomputable def hellingerDiv (a : ℝ) (μ ν : Measure α) : EReal := fDiv (hellingerFun a) μ ν

lemma hellingerDiv_zero (μ ν : Measure α) :
    hellingerDiv 0 μ ν = ν {x | ((∂μ/∂ν) x).toReal = 0} := by
  have h_eq : (fun x ↦ Set.indicator {0} 1 (μ.rnDeriv ν x).toReal)
      = {y | ((∂μ/∂ν) y).toReal = 0}.indicator (1 : α → ℝ) := by
    simp_rw [← Set.indicator_comp_right fun x ↦ ((∂μ/∂ν) x).toReal, Set.preimage,
      Set.mem_singleton_iff, Pi.one_comp]
  have h_meas : MeasurableSet {y | (μ.rnDeriv ν y).toReal = 0} := by
    apply measurableSet_eq_fun <;> fun_prop
  by_cases h_int : Integrable (fun x ↦ hellingerFun 0 (μ.rnDeriv ν x).toReal) ν
  swap
  · rw [hellingerDiv, fDiv_of_not_integrable h_int]
    rw [hellingerFun_zero'', h_eq, integrable_indicator_iff h_meas] at h_int
    have := integrableOn_const.mpr.mt h_int
    simp only [not_or, not_lt, top_le_iff] at this
    rw [this.2, EReal.coe_ennreal_top]
  rw [hellingerDiv, fDiv_of_integrable h_int, hellingerFun_zero'', h_eq, ← hellingerFun_zero'',
    derivAtTop_hellingerFun_of_lt_one zero_lt_one, zero_mul, add_zero,
    integral_indicator_one h_meas]
  rw [hellingerFun_zero'', h_eq, integrable_indicator_iff h_meas, Pi.one_def] at h_int
  apply integrableOn_const.mp at h_int
  simp only [one_ne_zero, false_or] at h_int
  exact EReal.coe_ennreal_toReal h_int.ne_top

lemma hellingerDiv_zero' (μ ν : Measure α) [SigmaFinite μ] :
    hellingerDiv 0 μ ν = ν {x | (∂μ/∂ν) x = 0} := by
  rw [hellingerDiv_zero]
  norm_cast
  refine measure_congr <| eventuallyEq_set.mpr ?_
  filter_upwards [μ.rnDeriv_lt_top ν] with x hx
  simp [ENNReal.toReal_eq_zero_iff, hx.ne]

lemma hellingerDiv_zero'' (μ ν : Measure α) [SigmaFinite μ] [IsFiniteMeasure ν] :
    hellingerDiv 0 μ ν = ν .univ - ν {x | 0 < (∂μ/∂ν) x} := by
  have h : {x | μ.rnDeriv ν x = 0} = {x | 0 < μ.rnDeriv ν x}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt, nonpos_iff_eq_zero, eq_comm]
  rw [hellingerDiv_zero', h,
    measure_compl (measurableSet_lt measurable_const (μ.measurable_rnDeriv _)) (measure_ne_top _ _),
    ENNReal.toEReal_sub (measure_ne_top _ _) (measure_mono _)]
  exact fun _ _ ↦ trivial

lemma hellingerDiv_zero_toReal (μ ν : Measure α) [SigmaFinite μ] [IsFiniteMeasure ν] :
    (hellingerDiv 0 μ ν).toReal = (ν .univ).toReal - (ν {x | 0 < (∂μ/∂ν) x}).toReal := by
  rw [hellingerDiv_zero'', EReal.toReal_sub]
  all_goals simp [measure_ne_top]

lemma hellingerDiv_zero_ne_top (μ ν : Measure α) [IsFiniteMeasure ν] :
    hellingerDiv 0 μ ν ≠ ⊤ := by
  rw [hellingerDiv_zero, ne_eq, EReal.coe_ennreal_eq_top_iff]
  exact measure_ne_top _ _

@[simp] lemma hellingerDiv_one (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    hellingerDiv 1 μ ν = kl μ ν := by
  rw [hellingerDiv, hellingerFun_one, kl_eq_fDiv]

@[simp]
lemma hellingerDiv_zero_measure_left (ν : Measure α) [IsFiniteMeasure ν] :
    hellingerDiv a 0 ν = (1 - a)⁻¹ * ν .univ := by
  rw [hellingerDiv, fDiv_zero_measure_left, hellingerFun_apply_zero]

@[simp]
lemma hellingerDiv_zero_measure_right_of_lt_one (ha : a < 1) (μ : Measure α) :
    hellingerDiv a μ 0 = 0 := by
  rw [hellingerDiv, fDiv_zero_measure_right, derivAtTop_hellingerFun_of_lt_one ha, zero_mul]

@[simp]
lemma hellingerDiv_zero_measure_right_of_one_le (ha : 1 ≤ a) (μ : Measure α) [hμ : NeZero μ] :
    hellingerDiv a μ 0 = ⊤ := by
  rw [hellingerDiv, fDiv_zero_measure_right, derivAtTop_hellingerFun_of_one_le ha,
    EReal.top_mul_of_pos]
  simp [hμ.out]

section HellingerEq

/--If `a ≤ 1` use `hellingerDiv_eq_integral_of_integrable_of_le_one` or
`hellingerDiv_eq_integral_of_le_one`, as they have fewer hypotheses.-/
lemma hellingerDiv_eq_integral_of_integrable_of_ac
    (h_int : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) (h_ac : 1 ≤ a → μ ≪ ν) :
    hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν := by
  rw [hellingerDiv, fDiv_of_integrable h_int]
  rcases (le_or_gt 1 a) with ha | ha
  · rw [Measure.singularPart_eq_zero_of_ac <| h_ac ha]
    norm_num
  · rw [derivAtTop_hellingerFun_of_lt_one ha]
    norm_num

lemma hellingerDiv_eq_integral_of_integrable_of_lt_one (ha : a < 1)
    (h_int : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν :=
  hellingerDiv_eq_integral_of_integrable_of_ac h_int ha.not_le.elim

lemma hellingerDiv_eq_integral_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν :=
  hellingerDiv_eq_integral_of_integrable_of_ac
    (integrable_hellingerFun_rnDeriv_of_lt_one ha_nonneg ha) ha.not_le.elim

lemma hellingerDiv_of_not_integrable
    (h : ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    hellingerDiv a μ ν = ⊤ :=
  fDiv_of_not_integrable h

lemma hellingerDiv_of_one_lt_not_ac (ha : 1 ≤ a) (h_ac : ¬ μ ≪ ν) [SigmaFinite μ] [SigmaFinite ν] :
    hellingerDiv a μ ν = ⊤ :=
  fDiv_of_not_ac (derivAtTop_hellingerFun_of_one_le ha) h_ac

lemma hellingerDiv_eq_top_iff (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    hellingerDiv a μ ν = ⊤
      ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∨ (1 ≤ a ∧ ¬ μ ≪ ν) := by
  constructor
  · contrapose!
    rintro ⟨h_int, h_ac⟩
    rw [hellingerDiv_eq_integral_of_integrable_of_ac h_int h_ac]
    exact EReal.coe_ne_top _
  · rintro (h | ⟨ha, h_ac⟩)
    · exact hellingerDiv_of_not_integrable h
    · exact hellingerDiv_of_one_lt_not_ac ha h_ac

lemma hellingerDiv_ne_top_iff (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    hellingerDiv a μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∧ (1 ≤ a → μ ≪ ν) := by
  rw [ne_eq, hellingerDiv_eq_top_iff]
  push_neg
  rfl

lemma hellingerDiv_eq_top_iff_of_one_le (ha : 1 ≤ a) (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] :
    hellingerDiv a μ ν = ⊤
      ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∨ ¬ μ ≪ ν := by
  rw [hellingerDiv_eq_top_iff, and_iff_right ha]

lemma hellingerDiv_ne_top_iff_of_one_le (ha : 1 ≤ a) (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] :
    hellingerDiv a μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν := by
  rw [ne_eq, hellingerDiv_eq_top_iff_of_one_le ha]
  push_neg
  rfl

lemma hellingerDiv_eq_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
    [SigmaFinite μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν = ⊤
      ↔ ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∨ ¬ μ ≪ ν := by
  rw [hellingerDiv_eq_top_iff_of_one_le ha.le, integrable_hellingerFun_iff_integrable_rpow ha.ne']

lemma hellingerDiv_ne_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
    [SigmaFinite μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∧ μ ≪ ν := by
  rw [hellingerDiv_ne_top_iff_of_one_le ha.le, integrable_hellingerFun_iff_integrable_rpow ha.ne']

lemma hellingerDiv_eq_top_iff_of_lt_one (ha : a < 1) (μ ν : Measure α) :
    hellingerDiv a μ ν = ⊤ ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  refine ⟨?_, fun h ↦ hellingerDiv_of_not_integrable h⟩
  contrapose!
  rintro h_int
  rw [hellingerDiv_eq_integral_of_integrable_of_lt_one ha h_int]
  exact EReal.coe_ne_top _

lemma hellingerDiv_ne_top_iff_of_lt_one (ha : a < 1) (μ ν : Measure α) :
    hellingerDiv a μ ν ≠ ⊤ ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  rw [ne_eq, hellingerDiv_eq_top_iff_of_lt_one ha, not_not]

lemma hellingerDiv_ne_top_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν ≠ ⊤ := by
  rw [hellingerDiv_ne_top_iff_of_lt_one ha]
  exact integrable_hellingerFun_rnDeriv_of_lt_one ha_nonneg ha

lemma hellingerDiv_ne_bot : hellingerDiv a μ ν ≠ ⊥ := by
  refine fDiv_ne_bot_of_derivAtTop_nonneg ?_
  by_cases ha : 1 ≤ a
  · rw [derivAtTop_hellingerFun_of_one_le ha]
    exact OrderTop.le_top 0
  · rw [derivAtTop_hellingerFun_of_lt_one (lt_of_not_ge ha)]

lemma hellingerDiv_eq_integral_of_ne_top [IsFiniteMeasure μ] [SigmaFinite ν]
    (h : hellingerDiv a μ ν ≠ ⊤) :
    hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν := by
  rw [hellingerDiv, fDiv_of_ne_top (by rwa [hellingerDiv] at h)]
  cases lt_or_le a 1 with
  | inl ha_lt => rw [derivAtTop_hellingerFun_of_lt_one ha_lt, zero_mul, add_zero]
  | inr ha_ge =>
    rw [hellingerDiv_ne_top_iff_of_one_le ha_ge] at h
    rw [Measure.singularPart_eq_zero_of_ac h.2]
    simp

/- Integral form of the Hellinger divergence:
`Hₐ(μ, ν) = (a - 1)⁻¹ ∫ (dμ/dν) ^ a dν - (a - 1)⁻¹ ν(α)`.
This lemma is not true for `a = 0`, because `0 ^ 0 = 1`. -/
lemma hellingerDiv_eq_integral_of_ne_top' (ha_ne_zero : a ≠ 0) (ha_ne_one : a ≠ 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : hellingerDiv a μ ν ≠ ⊤) :
    hellingerDiv a μ ν = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ * ν .univ := by
  rw [hellingerDiv_eq_integral_of_ne_top h]
  simp_rw [hellingerFun_of_ne_zero_of_ne_one ha_ne_zero ha_ne_one, integral_mul_left]
  rw [integral_sub _ (integrable_const _), integral_const, smul_eq_mul, mul_one, mul_sub,
    EReal.coe_sub, EReal.coe_mul, EReal.coe_mul, EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  rw [← integrable_hellingerFun_iff_integrable_rpow ha_ne_one]
  by_contra h_not_int
  exact h (hellingerDiv_of_not_integrable h_not_int)

lemma hellingerDiv_eq_integral_of_ne_top'' (ha_ne_zero : a ≠ 0) (ha_ne_one : a ≠ 1)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (h : hellingerDiv a μ ν ≠ ⊤) :
    hellingerDiv a μ ν = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ := by
  rw [hellingerDiv_eq_integral_of_ne_top' ha_ne_zero ha_ne_one h]
  simp

lemma hellingerDiv_eq_integral_of_lt_one' (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ * ν .univ :=
  hellingerDiv_eq_integral_of_ne_top' ha_pos.ne.symm ha.ne
    (hellingerDiv_ne_top_of_lt_one ha_pos.le ha μ ν)

lemma hellingerDiv_toReal_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (hellingerDiv a μ ν).toReal
      = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ * (ν .univ).toReal := by
  rw [hellingerDiv_eq_integral_of_lt_one' ha_pos ha, EReal.toReal_sub]
  · simp [EReal.toReal_mul]
  · exact EReal.coe_mul _ _ ▸ EReal.coe_ne_top _
  · exact EReal.coe_mul _ _ ▸  EReal.coe_ne_bot _
  · simp [ne_eq, EReal.mul_eq_top, measure_ne_top]
  · simp [ne_eq, EReal.mul_eq_bot, measure_ne_top]

lemma hellingerDiv_of_mutuallySingular_of_one_le (ha : 1 ≤ a) [NeZero μ]
    [SigmaFinite μ] [IsFiniteMeasure ν] (hμν : μ ⟂ₘ ν) :
    hellingerDiv a μ ν = ⊤ := by
  have := fDiv_of_mutuallySingular hμν (f := hellingerFun a)
  rw [hellingerDiv, this, derivAtTop_hellingerFun_of_one_le ha,
    EReal.top_mul_ennreal_coe (NeZero.ne' (μ .univ)).symm]
  apply EReal.add_top_of_ne_bot
  rw [ne_eq, EReal.mul_eq_bot, hellingerFun_apply_zero]
  simp [measure_ne_top]

lemma hellingerDiv_of_mutuallySingular_of_lt_one (ha : a < 1)
    [SigmaFinite μ] [IsFiniteMeasure ν] (hμν : μ ⟂ₘ ν) :
    hellingerDiv a μ ν = (1 - a)⁻¹ * ν .univ  := by
  rw [hellingerDiv, fDiv_of_mutuallySingular hμν, derivAtTop_hellingerFun_of_lt_one ha,
    hellingerFun_apply_zero, zero_mul, add_zero]

end HellingerEq

--Maybe we could write something like this for the conditional case? Would it be useful?
lemma hellingerDiv_le_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν ≤ (1 - a)⁻¹ * ν .univ := by
  by_cases h_zero : a = 0
  · rw [h_zero, hellingerDiv_zero']
    simp only [inv_one, EReal.coe_one, one_mul, EReal.coe_ennreal_le_coe_ennreal_iff, sub_zero]
    exact measure_mono fun _ _ ↦ trivial
  rw [hellingerDiv]
  refine (fDiv_le_zero_add_top (stronglyMeasurable_hellingerFun ha_nonneg)
    (convexOn_hellingerFun ha_nonneg)).trans_eq ?_
  rw [derivAtTop_hellingerFun_of_lt_one ha, zero_mul, add_zero,
    hellingerFun_of_ne_zero_of_ne_one h_zero ha.ne]
  simp only [zero_sub, mul_neg, mul_one, zero_mul, add_zero, zero_rpow h_zero]
  rw [neg_inv, neg_sub]

lemma hellingerDiv_symm' (ha_pos : 0 < a) (ha : a < 1) (h_eq : μ .univ = ν .univ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (1 - a) * hellingerDiv a μ ν = a * hellingerDiv (1 - a) ν μ := by
  rw [hellingerDiv_eq_integral_of_lt_one' ha_pos ha, hellingerDiv_eq_integral_of_lt_one']
  rotate_left
  · linarith
  · linarith
  simp only [sub_sub_cancel_left]
  simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), h_eq]
  norm_cast
  simp_rw [mul_sub, ← mul_assoc]
  have : (1 - a) * (a - 1)⁻¹ = a * (-a)⁻¹ := by
    rw [← neg_neg (1 - a), neg_sub, neg_mul, mul_inv_cancel₀, inv_neg, mul_comm, neg_mul,
      inv_mul_cancel₀ ha_pos.ne']
    linarith
  rw [integral_rpow_rnDeriv ha_pos ha.ne]
  congr

lemma hellingerDiv_symm (ha_pos : 0 < a) (ha : a < 1)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (1 - a) * hellingerDiv a μ ν = a * hellingerDiv (1 - a) ν μ :=
  hellingerDiv_symm' ha_pos ha (by simp)

lemma hellingerDiv_zero_nonneg (μ ν : Measure α) :
    0 ≤ hellingerDiv 0 μ ν := hellingerDiv_zero _ _ ▸ EReal.coe_ennreal_nonneg _

lemma hellingerDiv_nonneg (ha_pos : 0 ≤ a) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ hellingerDiv a μ ν := by
  by_cases h_zero : a = 0
  · exact h_zero ▸ hellingerDiv_zero_nonneg μ ν
  replace ha_pos := ha_pos.lt_of_ne fun h ↦ h_zero h.symm
  rw [hellingerDiv]
  exact fDiv_nonneg (convexOn_hellingerFun ha_pos.le) (continuous_hellingerFun ha_pos).continuousOn
    hellingerFun_apply_one_eq_zero

section MeasUnivAddMulHellingerDiv
/-! In this section there are results about the expression `ν(α) + (a - 1) * Hₐ(μ, ν)`,
which appears in the definition of the Renyi divergence. -/

lemma meas_univ_add_mul_hellingerDiv_eq (ha_ne_zero : a ≠ 0) (ha_ne_one : a ≠ 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : hellingerDiv a μ ν ≠ ⊤) :
    ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν = ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν := by
  rw_mod_cast [hellingerDiv_eq_integral_of_ne_top' ha_ne_zero ha_ne_one h,
    ← ENNReal.ofReal_toReal (measure_ne_top ν .univ), EReal.coe_ennreal_ofReal,
    max_eq_left ENNReal.toReal_nonneg, ← mul_sub, ← mul_assoc, mul_inv_cancel₀ _]
  ring_nf
  exact sub_ne_zero_of_ne ha_ne_one

lemma meas_univ_add_mul_hellingerDiv_zero_eq (ha : a = 0) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν = ν {x | 0 < (∂μ/∂ν) x} := by
  simp only [ha, EReal.coe_zero, zero_sub, hellingerDiv_zero'', neg_mul, one_mul, rpow_zero,
    integral_const, smul_eq_mul, mul_one]
  rw [EReal.neg_sub, ← add_assoc, ← sub_eq_add_neg, EReal.sub_self, zero_add]
  all_goals simp [measure_ne_top]

lemma meas_univ_add_mul_hellingerDiv_nonneg_of_le_one (ha_nonneg : 0 ≤ a) (ha : a ≤ 1)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν := by
  by_cases h_one : a = 1
  · have : (1 - 1 : EReal) = 0 := EReal.sub_self (ne_of_beq_false rfl) (ne_of_beq_false rfl)
    simp [h_one, add_zero, zero_mul, this, EReal.coe_ennreal_nonneg]
  replace ha : a < 1 := ha.lt_of_ne h_one
  calc
    _ = (ν .univ) - (1 - ↑a) * hellingerDiv a μ ν := by
      congr
      rw [← neg_mul, EReal.neg_sub _ _, add_comm, sub_eq_add_neg] <;> simp
    _ ≥ (ν .univ) - (1 - ↑a) * ((1 - a)⁻¹ * ν .univ) := by
      simp_rw [sub_eq_add_neg]
      gcongr
      rw [EReal.neg_le_neg_iff]
      gcongr
      · norm_cast
        simp only [le_add_neg_iff_add_le, zero_add, ha.le]
      · exact hellingerDiv_le_of_lt_one ha_nonneg ha μ ν
    _ = (ν .univ) - (ν .univ) := by
      norm_cast
      rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ (by linarith), EReal.coe_one, one_mul]
    _ ≥ _ := by
      rw [← ENNReal.toEReal_sub (measure_ne_top _ _) (le_refl _)]
      simp

lemma meas_univ_add_mul_hellingerDiv_nonneg_of_one_lt (ha : 1 < a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν := by
  by_cases h_top : hellingerDiv a μ ν = ⊤
  · rw [h_top, EReal.mul_top_of_pos, EReal.add_top_of_ne_bot (EReal.coe_ennreal_ne_bot _)]
    · exact OrderTop.le_top 0
    · norm_cast
      linarith
  rw [meas_univ_add_mul_hellingerDiv_eq (by linarith) ha.ne' h_top]
  simp only [ge_iff_le, EReal.coe_nonneg]
  positivity

lemma meas_univ_add_mul_hellingerDiv_nonneg (ha_nonneg : 0 ≤ a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν := by
  by_cases h_le_one : a ≤ 1
  · exact meas_univ_add_mul_hellingerDiv_nonneg_of_le_one ha_nonneg h_le_one μ ν
  · exact meas_univ_add_mul_hellingerDiv_nonneg_of_one_lt
      (lt_of_not_ge h_le_one) μ ν

lemma meas_univ_add_mul_hellingerDiv_eq_zero_iff (ha_ne_one : a ≠ 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
  ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν = 0 ↔ μ ⟂ₘ ν ∧ hellingerDiv a μ ν ≠ ⊤ := by
  by_cases h_top : hellingerDiv a μ ν = ⊤
  · simp only [h_top, ne_eq, not_true_eq_false, and_false, iff_false]
    rcases (lt_or_gt_of_ne ha_ne_one) with ha | ha
    · rw [EReal.mul_top_of_neg (by exact_mod_cast sub_neg.mpr ha), EReal.add_bot]
      exact EReal.bot_ne_zero
    · rw [EReal.mul_top_of_pos (by exact_mod_cast sub_pos.mpr ha),
        EReal.add_top_of_ne_bot (EReal.coe_ennreal_ne_bot _)]
      exact EReal.top_ne_zero
  simp_rw [ne_eq, h_top, not_false_eq_true, and_true]
  by_cases ha_zero : a = 0
  · rw [meas_univ_add_mul_hellingerDiv_zero_eq ha_zero, ← Measure.rnDeriv_eq_zero,
      EReal.coe_ennreal_eq_zero]
    simp_rw [← not_le, ← ae_iff]
    exact eventually_congr <| .of_forall <| fun _ ↦ nonpos_iff_eq_zero
  rw [meas_univ_add_mul_hellingerDiv_eq ha_zero ha_ne_one h_top]
  norm_cast
  refine integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular ha_zero ?_
  rw [← integrable_hellingerFun_iff_integrable_rpow ha_ne_one]
  exact integrable_of_fDiv_ne_top h_top

lemma meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_lt_one (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν = 0 ↔ μ ⟂ₘ ν  := by
  rw [meas_univ_add_mul_hellingerDiv_eq_zero_iff ha.ne, and_iff_left_iff_imp]
  intro hμν
  rw [hellingerDiv_of_mutuallySingular_of_lt_one ha hμν, ne_eq, EReal.mul_eq_top]
  simp [measure_ne_top]

lemma meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_one_lt (ha : 1 < a)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν = 0 ↔ μ = 0 := by
  rw [meas_univ_add_mul_hellingerDiv_eq_zero_iff ha.ne', hellingerDiv_ne_top_iff_of_one_le ha.le]
  refine ⟨fun ⟨h, _, h'⟩ ↦ Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h' h,
    fun h ↦ ?_⟩
  simp only [h, Measure.MutuallySingular.zero_left, Measure.AbsolutelyContinuous.zero, and_true,
    true_and]
  apply Integrable.congr (show Integrable (fun _ ↦ hellingerFun a 0) ν from integrable_const _)
  filter_upwards [ν.rnDeriv_zero] with x hx
  simp [hx]

lemma toENNReal_meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_lt_one
    (ha_nonneg : 0 ≤ a) (ha : a < 1) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (↑(ν .univ) + (a - 1) * (hellingerDiv a μ ν)).toENNReal = 0 ↔ μ ⟂ₘ ν  := by
  rw [← meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_lt_one ha, EReal.toENNReal_eq_zero_iff]
  exact LE.le.le_iff_eq (meas_univ_add_mul_hellingerDiv_nonneg ha_nonneg μ ν)

lemma toENNReal_meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_one_lt (ha : 1 < a)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (↑(ν .univ) + (a - 1) * (hellingerDiv a μ ν)).toENNReal = 0 ↔ μ = 0  := by
  rw [← meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_one_lt ha (ν := ν),
    EReal.toENNReal_eq_zero_iff]
  exact LE.le.le_iff_eq (meas_univ_add_mul_hellingerDiv_nonneg (by positivity) μ ν)

lemma meas_univ_add_mul_hellingerDiv_ne_top_of_lt_one (ha : a < 1) [IsFiniteMeasure ν] :
    ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν ≠ ⊤ := by
  apply EReal.add_ne_top
  · simp [measure_ne_top]
  · rw [ne_eq, EReal.mul_eq_top]
    norm_cast
    simp_rw [EReal.coe_ne_bot, EReal.coe_ne_top, sub_neg, sub_pos, ha, not_lt_of_gt ha,
      hellingerDiv_ne_bot]
    tauto

lemma meas_univ_add_mul_hellingerDiv_eq_top_iff_of_one_lt (ha : 1 < a)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν = ⊤
      ↔ ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∨ ¬ μ ≪ ν := by
  rw [← integrable_hellingerFun_iff_integrable_rpow ha.ne',
    ← hellingerDiv_eq_top_iff_of_one_le ha.le]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose! h
    refine EReal.add_ne_top ?_ ?_
    · rw [ne_eq, EReal.coe_ennreal_eq_top_iff]
      exact measure_ne_top ν .univ
    · rw [ne_eq, EReal.mul_eq_top]
      norm_cast
      simp_rw [EReal.coe_ne_bot, EReal.coe_ne_top, sub_neg, sub_pos, ha, not_lt_of_gt ha,
      hellingerDiv_ne_bot]
      tauto
  · rw [h, EReal.mul_top_of_pos (by exact_mod_cast sub_pos.mpr ha), EReal.add_top_of_ne_bot]
    exact EReal.coe_ennreal_ne_bot _

end MeasUnivAddMulHellingerDiv

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β}

lemma le_hellingerDiv_compProd [CountableOrCountablyGenerated α β] (ha_pos : 0 < a)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    hellingerDiv a μ ν ≤ hellingerDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) :=
  le_fDiv_compProd μ ν κ η (stronglyMeasurable_hellingerFun ha_pos.le)
    (convexOn_hellingerFun ha_pos.le) (continuous_hellingerFun ha_pos).continuousOn

lemma hellingerDiv_fst_le [Nonempty β] [StandardBorelSpace β] (ha_pos : 0 < a)
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ.fst ν.fst ≤ hellingerDiv a μ ν :=
  fDiv_fst_le _ _ (stronglyMeasurable_hellingerFun ha_pos.le)
    (convexOn_hellingerFun ha_pos.le) (continuous_hellingerFun ha_pos).continuousOn

lemma hellingerDiv_snd_le [Nonempty α] [StandardBorelSpace α] (ha_pos : 0 < a)
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ.snd ν.snd ≤ hellingerDiv a μ ν :=
  fDiv_snd_le _ _ (stronglyMeasurable_hellingerFun ha_pos.le)
    (convexOn_hellingerFun ha_pos.le) (continuous_hellingerFun ha_pos).continuousOn

lemma hellingerDiv_comp_le_compProd [Nonempty α] [StandardBorelSpace α] (ha_pos : 0 < a)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    hellingerDiv a (κ ∘ₘ μ) (η ∘ₘ ν) ≤ hellingerDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) :=
  fDiv_comp_le_compProd μ ν κ η (stronglyMeasurable_hellingerFun ha_pos.le)
    (convexOn_hellingerFun ha_pos.le) (continuous_hellingerFun ha_pos).continuousOn

/--The Data Processing Inequality for the Hellinger divergence. -/
lemma hellingerDiv_comp_right_le [Nonempty α] [StandardBorelSpace α] (ha_pos : 0 < a)
    [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    hellingerDiv a (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ hellingerDiv a μ ν :=
  fDiv_comp_right_le μ ν κ (stronglyMeasurable_hellingerFun ha_pos.le)
    (convexOn_hellingerFun ha_pos.le) (continuous_hellingerFun ha_pos).continuousOn

end DataProcessingInequality

end ProbabilityTheory

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.Hellinger.HellingerDivFun
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

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

-- TODO: with the refactor, we loose `hellingerDiv 0 μ ν = ν {x | (∂μ/∂ν) x = 0}` and get
-- the zero divergence instead.

/-- Hellinger divergence of order `a`.
The cases `a = 0` and `a = 1` are defined separately inside the definition of the Hellinger
function, so that in the case `a = 0` we have `hellingerDiv 0 μ ν = ν {x | (∂μ/∂ν) x = 0}`, and in
the case `a = 1` the Hellinger divergence coincides with the KL divergence. -/
noncomputable def hellingerDiv (a : ℝ) (μ ν : Measure α) : ℝ≥0∞ := fDiv (hellingerDivFun a) μ ν

-- lemma hellingerDiv_zero (μ ν : Measure α) :
--     hellingerDiv 0 μ ν = ν {x | ((∂μ/∂ν) x).toReal = 0} := by
--   have h_eq : (fun x ↦ Set.indicator {0} 1 (μ.rnDeriv ν x).toReal)
--       = {y | ((∂μ/∂ν) y).toReal = 0}.indicator (1 : α → ℝ) := by
--     simp_rw [← Set.indicator_comp_right fun x ↦ ((∂μ/∂ν) x).toReal, Set.preimage,
--       Set.mem_singleton_iff, Pi.one_comp]
--   have h_meas : MeasurableSet {y | (μ.rnDeriv ν y).toReal = 0} := by
--     apply measurableSet_eq_fun <;> fun_prop
--   by_cases h_int : Integrable (fun x ↦ hellingerFun 0 (μ.rnDeriv ν x).toReal) ν
--   swap
--   · rw [hellingerDiv, fDiv_of_not_integrable h_int]
--     rw [hellingerFun_zero'', h_eq, integrable_indicator_iff h_meas] at h_int
--     have := integrableOn_const.mpr.mt h_int
--     simp only [not_or, not_lt, top_le_iff] at this
--     rw [this.2, EReal.coe_ennreal_top]
--   rw [hellingerDiv, fDiv_of_integrable h_int, hellingerFun_zero'', h_eq, ← hellingerFun_zero'',
--     derivAtTop_hellingerFun_of_lt_one zero_lt_one, zero_mul, add_zero,
--     integral_indicator_one h_meas]
--   rw [hellingerFun_zero'', h_eq, integrable_indicator_iff h_meas, Pi.one_def] at h_int
--   apply integrableOn_const.mp at h_int
--   simp only [one_ne_zero, false_or] at h_int
--   exact EReal.coe_ennreal_toReal h_int.ne_top

-- lemma hellingerDiv_zero' (μ ν : Measure α) [SigmaFinite μ] :
--     hellingerDiv 0 μ ν = ν {x | (∂μ/∂ν) x = 0} := by
--   rw [hellingerDiv_zero]
--   norm_cast
--   refine measure_congr <| eventuallyEq_set.mpr ?_
--   filter_upwards [μ.rnDeriv_lt_top ν] with x hx
--   simp [ENNReal.toReal_eq_zero_iff, hx.ne]

-- lemma hellingerDiv_zero'' (μ ν : Measure α) [SigmaFinite μ] [IsFiniteMeasure ν] :
--     hellingerDiv 0 μ ν = ν .univ - ν {x | 0 < (∂μ/∂ν) x} := by
--   have h : {x | μ.rnDeriv ν x = 0} = {x | 0 < μ.rnDeriv ν x}ᶜ := by
--     ext x
--     simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt, nonpos_iff_eq_zero, eq_comm]
--   rw [hellingerDiv_zero', h,
--     measure_compl (measurableSet_lt measurable_const (μ.measurable_rnDeriv _)) (measure_ne_top _ _),
--     ENNReal.toEReal_sub (measure_ne_top _ _) (measure_mono _)]
--   exact fun _ _ ↦ trivial

-- lemma hellingerDiv_zero_toReal (μ ν : Measure α) [SigmaFinite μ] [IsFiniteMeasure ν] :
--     (hellingerDiv 0 μ ν).toReal = (ν .univ).toReal - (ν {x | 0 < (∂μ/∂ν) x}).toReal := by
--   rw [hellingerDiv_zero'', EReal.toReal_sub]
--   all_goals simp [measure_ne_top]

-- lemma hellingerDiv_zero_ne_top (μ ν : Measure α) [IsFiniteMeasure ν] :
--     hellingerDiv 0 μ ν ≠ ⊤ := by
--   rw [hellingerDiv_zero, ne_eq, EReal.coe_ennreal_eq_top_iff]
--   exact measure_ne_top _ _

@[simp] lemma hellingerDiv_of_nonpos (ha : a ≤ 0) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν = 0 := by
  rw [hellingerDiv, hellingerDivFun_of_nonpos ha, fDiv_zero]

lemma hellingerDiv_zero [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv 0 μ ν = 0 := by simp

@[simp] lemma hellingerDiv_one (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv 1 μ ν = kl μ ν := by
  rw [hellingerDiv, hellingerDivFun_one, kl_eq_fDiv]

@[simp]
lemma hellingerDiv_zero_measure_left (ha_pos : 0 < a) (ν : Measure α) [IsFiniteMeasure ν] :
    hellingerDiv a 0 ν = ν .univ := by
  rw [hellingerDiv, fDiv_zero_measure_left, hellingerDivFun_apply_zero_of_pos ha_pos, one_mul]

@[simp]
lemma hellingerDiv_zero_measure_right_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ : Measure α) :
    hellingerDiv a μ 0 = ENNReal.ofReal (a * (1 - a)⁻¹) * μ Set.univ := by
  rw [hellingerDiv, fDiv_zero_measure_right, derivAtTop_hellingerDivFun_of_lt_one ha_pos ha]

@[simp]
lemma hellingerDiv_zero_measure_right_of_one_le (ha : 1 ≤ a) (μ : Measure α) [hμ : NeZero μ] :
    hellingerDiv a μ 0 = ∞ := by
  rw [hellingerDiv, fDiv_zero_measure_right, derivAtTop_hellingerDivFun_of_one_le ha]
  simp [hμ.out]

section HellingerEq

lemma hellingerDiv_eq_integral_of_integrable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1) (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν) :
    hellingerDiv a μ ν
      = ENNReal.ofReal ((a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * (ν.withDensity (μ.rnDeriv ν) .univ).toReal)
        + (hellingerDivFun a).derivAtTop * μ.singularPart ν .univ := by
  have h := ν.rnDeriv_withDensity (μ.measurable_rnDeriv ν)
  rw [hellingerDiv, fDiv_eq_add_withDensity_derivAtTop, fDiv_of_absolutelyContinuous,
    lintegral_hellingerDivFun_of_pos_of_ne_one_of_integrable_of_ac ha_pos ha_ne]
  · congr 5
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx
    rw [hx]
  · refine (integrable_congr ?_).mp h_int
    filter_upwards [h] with x hx
    rw [hx]
  · exact withDensity_absolutelyContinuous _ _
  · exact withDensity_absolutelyContinuous _ _

lemma hellingerDiv_eq_integral_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_lt : a < 1) :
    hellingerDiv a μ ν
      = ENNReal.ofReal ((a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * (μ .univ).toReal) := by
  rw [hellingerDiv_eq_integral_of_integrable ha_pos ha_lt.ne
      (integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha_lt),
    derivAtTop_hellingerDivFun_of_lt_one ha_pos ha_lt]
  have : (μ.singularPart ν) Set.univ = ENNReal.ofReal ((μ.singularPart ν) Set.univ).toReal := by
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [this, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add, add_assoc]
  · congr 2
    rw [mul_comm a, ← mul_add, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
    simp
  · have h := integral_hellingerFun_rnDeriv_nonneg_of_ac ha_pos ha_lt
      (withDensity_absolutelyContinuous ν (μ.rnDeriv ν))
    convert h using 4
    refine integral_congr_ae ?_
    have h := ν.rnDeriv_withDensity (μ.measurable_rnDeriv ν)
    filter_upwards [h] with x hx
    rw [hx]
  · refine mul_nonneg (mul_nonneg ha_pos.le ?_) ENNReal.toReal_nonneg
    simp [ha_lt.le]
  · refine mul_nonneg ha_pos.le ?_
    simp [ha_lt.le]

lemma hellingerDiv_ne_top_of_lt_one (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν ≠ ∞ := by
  rcases le_or_lt a 0 with (ha0 | ha0)
  · simp [ha0]
  rw [hellingerDiv_eq_integral_of_lt_one ha0 ha]
  simp

-- /--If `a ≤ 1` use `hellingerDiv_eq_integral_of_integrable_of_le_one` or
-- `hellingerDiv_eq_integral_of_le_one`, as they have fewer hypotheses.-/
-- lemma hellingerDiv_eq_integral_of_integrable_of_ac
--     (h_int : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) (h_ac : 1 ≤ a → μ ≪ ν) :
--     hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν := by
--   rw [hellingerDiv, fDiv_of_integrable h_int]
--   rcases (le_or_gt 1 a) with ha | ha
--   · rw [Measure.singularPart_eq_zero_of_ac <| h_ac ha]
--     norm_num
--   · rw [derivAtTop_hellingerFun_of_lt_one ha]
--     norm_num

-- lemma hellingerDiv_eq_integral_of_integrable_of_lt_one (ha : a < 1)
--     (h_int : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
--     hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν :=
--   hellingerDiv_eq_integral_of_integrable_of_ac h_int ha.not_le.elim

-- lemma hellingerDiv_eq_integral_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) (μ ν : Measure α)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν :=
--   hellingerDiv_eq_integral_of_integrable_of_ac
--     (integrable_hellingerFun_rnDeriv_of_lt_one ha_nonneg ha) ha.not_le.elim

lemma lintegral_hellingerDivFun_eq_top_of_not_integrable [SigmaFinite μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_one : a ≠ 1)
    (h : ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) :
    ∫⁻ x, hellingerDivFun a ((∂μ/∂ν) x) ∂ν = ∞ := by
  rw [← integrable_hellingerFun_iff_integrable_rpow ha_one] at h
  simp [hellingerDivFun, (not_le.mpr ha_pos), ha_one]
  exact lintegral_ofReal_eq_top_of_not_integrable h

lemma hellingerDiv_of_not_integrable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha : 0 ≤ a)
    (h : ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    hellingerDiv a μ ν = ∞ := by
  by_cases ha_zero : a = 0
  · simp only [ha_zero, le_refl, hellingerDiv_of_nonpos, ENNReal.zero_ne_top]
    refine h ?_
    simp only [ha_zero, hellingerFun_zero]
    sorry
  have ha_pos : 0 < a := ha.lt_of_ne (Ne.symm ha_zero)
  by_cases ha_one : a = 1
  · simp only [ha_one, hellingerDiv_one]
    rw [kl_eq_top_iff]
    intro hμν
    rwa [ha_one, integrable_hellingerFun_one_iff hμν] at h
  refine fDiv_of_lintegral_eq_top ?_
  simp [hellingerDivFun, (not_le.mpr ha_pos), ha_one]
  exact lintegral_ofReal_eq_top_of_not_integrable h

lemma hellingerDiv_of_one_lt_not_ac (ha : 1 ≤ a) (h_ac : ¬ μ ≪ ν)
    [SigmaFinite μ] [SigmaFinite ν] :
    hellingerDiv a μ ν = ∞ :=
  fDiv_of_not_ac (derivAtTop_hellingerDivFun_of_one_le ha) h_ac

lemma hellingerDiv_eq_top_iff (μ ν : Measure α) [IsFiniteMeasure μ] [SigmaFinite ν] :
    hellingerDiv a μ ν = ∞
      ↔ ∫⁻ x, hellingerDivFun a ((∂μ/∂ν) x) ∂ν = ∞ ∨ (1 ≤ a ∧ ¬ μ ≪ ν) := by
  rw [hellingerDiv, fDiv_eq_top_iff, derivAtTop_hellingerDivFun_eq_top_iff]

lemma hellingerDiv_ne_top_iff (μ ν : Measure α) [IsFiniteMeasure μ] [SigmaFinite ν] :
    hellingerDiv a μ ν ≠ ∞
      ↔ ∫⁻ x, hellingerDivFun a ((∂μ/∂ν) x) ∂ν ≠ ∞ ∧ (1 ≤ a → μ ≪ ν) := by
  rw [ne_eq, hellingerDiv_eq_top_iff]
  push_neg
  rfl

lemma hellingerDiv_eq_top_iff_of_one_le (ha : 1 ≤ a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    hellingerDiv a μ ν = ∞
      ↔ ∫⁻ x, hellingerDivFun a ((∂μ/∂ν) x) ∂ν = ∞ ∨ ¬ μ ≪ ν := by
  rw [hellingerDiv_eq_top_iff, and_iff_right ha]

lemma hellingerDiv_ne_top_iff_of_one_le (ha : 1 ≤ a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    hellingerDiv a μ ν ≠ ∞
      ↔ ∫⁻ x, hellingerDivFun a ((∂μ/∂ν) x) ∂ν ≠ ∞ ∧ μ ≪ ν := by
  rw [ne_eq, hellingerDiv_eq_top_iff_of_one_le ha]
  push_neg
  rfl

-- lemma hellingerDiv_eq_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     hellingerDiv a μ ν = ∞
--       ↔ ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∨ ¬ μ ≪ ν := by
--   rw [hellingerDiv_eq_top_iff_of_one_le ha.le, ← integrable_hellingerFun_iff_integrable_rpow ha.ne']

-- lemma hellingerDiv_ne_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     hellingerDiv a μ ν ≠ ∞
--       ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∧ μ ≪ ν := by
--   rw [hellingerDiv_ne_top_iff_of_one_le ha.le, integrable_hellingerFun_iff_integrable_rpow ha.ne']

-- lemma hellingerDiv_eq_top_iff_of_lt_one (ha : a < 1) (μ ν : Measure α) :
--     hellingerDiv a μ ν = ∞ ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
--   refine ⟨?_, fun h ↦ hellingerDiv_of_not_integrable h⟩
--   contrapose!
--   rintro h_int
--   rw [hellingerDiv_eq_integral_of_integrable_of_lt_one ha h_int]
--   exact EReal.coe_ne_top _

-- lemma hellingerDiv_ne_top_iff_of_lt_one (ha : a < 1) (μ ν : Measure α) :
--     hellingerDiv a μ ν ≠ ∞ ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
--   rw [ne_eq, hellingerDiv_eq_top_iff_of_lt_one ha, not_not]

-- lemma hellingerDiv_ne_bot : hellingerDiv a μ ν ≠ ⊥ := by
--   refine fDiv_ne_bot_of_derivAtTop_nonneg ?_
--   by_cases ha : 1 ≤ a
--   · rw [derivAtTop_hellingerFun_of_one_le ha]
--     exact OrderTop.le_top 0
--   · rw [derivAtTop_hellingerFun_of_lt_one (lt_of_not_ge ha)]

-- lemma hellingerDiv_eq_integral_of_ne_top [IsFiniteMeasure μ] [SigmaFinite ν]
--     (h : hellingerDiv a μ ν ≠ ∞) :
--     hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν := by
--   rw [hellingerDiv, fDiv_of_ne_top (by rwa [hellingerDiv] at h)]
--   cases lt_or_le a 1 with
--   | inl ha_lt => rw [derivAtTop_hellingerFun_of_lt_one ha_lt, zero_mul, add_zero]
--   | inr ha_ge =>
--     rw [hellingerDiv_ne_top_iff_of_one_le ha_ge] at h
--     rw [Measure.singularPart_eq_zero_of_ac h.2]
--     simp

-- /- Integral form of the Hellinger divergence:
-- `Hₐ(μ, ν) = (a - 1)⁻¹ ∫ (dμ/dν) ^ a dν - (a - 1)⁻¹ ν(α)`.
-- This lemma is not true for `a = 0`, because `0 ^ 0 = 1`. -/
-- lemma hellingerDiv_eq_integral_of_ne_top' (ha_ne_zero : a ≠ 0) (ha_ne_one : a ≠ 1)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : hellingerDiv a μ ν ≠ ∞) :
--     hellingerDiv a μ ν = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ * ν .univ := by
--   rw [hellingerDiv_eq_integral_of_ne_top h]
--   simp_rw [hellingerFun_of_ne_zero_of_ne_one ha_ne_zero ha_ne_one, integral_mul_left]
--   rw [integral_sub _ (integrable_const _), integral_const, smul_eq_mul, mul_one, mul_sub,
--     EReal.coe_sub, EReal.coe_mul, EReal.coe_mul, EReal.coe_ennreal_toReal (measure_ne_top _ _)]
--   rw [← integrable_hellingerFun_iff_integrable_rpow ha_ne_one]
--   by_contra h_not_int
--   exact h (hellingerDiv_of_not_integrable h_not_int)

-- lemma hellingerDiv_eq_integral_of_ne_top'' (ha_ne_zero : a ≠ 0) (ha_ne_one : a ≠ 1)
--     [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (h : hellingerDiv a μ ν ≠ ∞) :
--     hellingerDiv a μ ν = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ := by
--   rw [hellingerDiv_eq_integral_of_ne_top' ha_ne_zero ha_ne_one h]
--   simp

-- lemma hellingerDiv_eq_integral_of_lt_one' (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     hellingerDiv a μ ν = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ * ν .univ :=
--   hellingerDiv_eq_integral_of_ne_top' ha_pos.ne.symm ha.ne
--     (hellingerDiv_ne_top_of_lt_one ha_pos.le ha μ ν)

-- lemma hellingerDiv_toReal_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     (hellingerDiv a μ ν).toReal
--       = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ * (ν .univ).toReal := by
--   rw [hellingerDiv_eq_integral_of_lt_one' ha_pos ha, EReal.toReal_sub]
--   · simp [EReal.toReal_mul]
--   · exact EReal.coe_mul _ _ ▸ EReal.coe_ne_top _
--   · exact EReal.coe_mul _ _ ▸  EReal.coe_ne_bot _
--   · simp [ne_eq, EReal.mul_eq_top, measure_ne_top]
--   · simp [ne_eq, EReal.mul_eq_bot, measure_ne_top]

lemma hellingerDiv_of_mutuallySingular_of_one_le (ha : 1 ≤ a) [hμ : NeZero μ]
    [SigmaFinite μ] [IsFiniteMeasure ν] (hμν : μ ⟂ₘ ν) :
    hellingerDiv a μ ν = ∞ := by
  have ha_pos : 0 < a := by positivity
  simp [ha_pos, not_le.mpr ha_pos, hellingerDiv, fDiv_of_mutuallySingular hμν, not_lt.mpr ha,
    hμ.out]

lemma hellingerDiv_of_mutuallySingular_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    [SigmaFinite μ] [IsFiniteMeasure ν] (hμν : μ ⟂ₘ ν) :
    hellingerDiv a μ ν = ν Set.univ + ENNReal.ofReal (a * (1 - a)⁻¹) * μ Set.univ := by
  rw [hellingerDiv, fDiv_of_mutuallySingular hμν, derivAtTop_hellingerDivFun_of_lt_one ha_pos ha,
    hellingerDivFun_apply_zero, if_neg (not_le.mpr ha_pos), one_mul]

end HellingerEq

--Maybe we could write something like this for the conditional case? Would it be useful?
lemma hellingerDiv_le_of_lt_one (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν ≤ ν Set.univ + ENNReal.ofReal (a * (1 - a)⁻¹) * μ Set.univ := by
  by_cases h_zero : a ≤ 0
  · simp [h_zero]
  refine fDiv_le_zero_add_top.trans_eq ?_
  simp [h_zero, ha]

lemma hellingerDiv_eq_add_measure_univ_iff_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν = ν Set.univ + ENNReal.ofReal (a * (1 - a)⁻¹) * μ Set.univ
      ↔ μ ⟂ₘ ν := by
  refine ⟨fun h ↦ ?_, hellingerDiv_of_mutuallySingular_of_lt_one ha_pos ha⟩
  rw [hellingerDiv_eq_integral_of_lt_one ha_pos ha] at h
  rw [← integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular (a := a) ha_pos.ne']
  swap; · exact integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha
  have h_eq : ν Set.univ + ENNReal.ofReal (a * (1 - a)⁻¹) * μ Set.univ
      = ENNReal.ofReal ((ν .univ).toReal + a * (1 - a)⁻¹ * (μ .univ).toReal) := by
    sorry
  rw [h_eq, ENNReal.ofReal_eq_ofReal_iff, add_assoc, mul_comm a, add_left_eq_self, mul_eq_zero,
    inv_eq_zero, sub_eq_zero] at h
  · simpa [ha.ne] using h
  · refine (integral_hellingerFun_rnDeriv_nonneg ha_pos ha (μ := μ) (ν := ν)).trans ?_
    refine add_le_add le_rfl ?_
    sorry
  · refine add_nonneg (by positivity) (mul_nonneg (mul_nonneg ha_pos.le ?_) (by positivity))
    simp [ha.le]

lemma hellingerDiv_symm' (ha_pos : 0 < a) (ha : a < 1) (h_eq : μ .univ = ν .univ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal.ofReal (1 - a) * hellingerDiv a μ ν = ENNReal.ofReal a * hellingerDiv (1 - a) ν μ := by
  sorry
  -- rw [hellingerDiv_eq_integral_of_lt_one' ha_pos ha, hellingerDiv_eq_integral_of_lt_one']
  -- rotate_left
  -- · linarith
  -- · linarith
  -- simp only [sub_sub_cancel_left]
  -- simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), h_eq]
  -- norm_cast
  -- simp_rw [mul_sub, ← mul_assoc]
  -- have : (1 - a) * (a - 1)⁻¹ = a * (-a)⁻¹ := by
  --   rw [← neg_neg (1 - a), neg_sub, neg_mul, mul_inv_cancel₀, inv_neg, mul_comm, neg_mul,
  --     inv_mul_cancel₀ ha_pos.ne']
  --   linarith
  -- rw [integral_rpow_rnDeriv ha_pos ha.ne]
  -- congr

lemma hellingerDiv_symm (ha_pos : 0 < a) (ha : a < 1)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (1 - a) * hellingerDiv a μ ν = ENNReal.ofReal a * hellingerDiv (1 - a) ν μ :=
  hellingerDiv_symm' ha_pos ha (by simp)

-- lemma hellingerDiv_zero_nonneg (μ ν : Measure α) :
--     0 ≤ hellingerDiv 0 μ ν := hellingerDiv_zero _ _ ▸ EReal.coe_ennreal_nonneg _

-- lemma hellingerDiv_nonneg (ha_pos : 0 ≤ a) (μ ν : Measure α)
--     [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
--     0 ≤ hellingerDiv a μ ν := by
--   by_cases h_zero : a = 0
--   · exact h_zero ▸ hellingerDiv_zero_nonneg μ ν
--   replace ha_pos := ha_pos.lt_of_ne fun h ↦ h_zero h.symm
--   rw [hellingerDiv]
--   exact fDiv_nonneg (convexOn_hellingerFun ha_pos.le) (continuous_hellingerFun ha_pos).continuousOn
--     hellingerFun_apply_one_eq_zero

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β}

lemma le_hellingerDiv_compProd [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    hellingerDiv a μ ν ≤ hellingerDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) :=
  le_fDiv_compProd μ ν κ η

lemma hellingerDiv_fst_le [Nonempty β] [StandardBorelSpace β]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ.fst ν.fst ≤ hellingerDiv a μ ν :=
  fDiv_fst_le _ _

lemma hellingerDiv_snd_le [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ.snd ν.snd ≤ hellingerDiv a μ ν :=
  fDiv_snd_le _ _

lemma hellingerDiv_comp_le_compProd [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    hellingerDiv a (κ ∘ₘ μ) (η ∘ₘ ν) ≤ hellingerDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) :=
  fDiv_comp_le_compProd μ ν κ η

/--The Data Processing Inequality for the Hellinger divergence. -/
lemma hellingerDiv_comp_right_le [Nonempty α] [StandardBorelSpace α]
    [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    hellingerDiv a (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ hellingerDiv a μ ν :=
  fDiv_comp_right_le μ ν κ

end DataProcessingInequality

-- section MeasUnivAddMulHellingerDiv
-- /-! In this section there are results about the expression `ν(α) + (a - 1) * Hₐ(μ, ν)`,
-- which appears in the definition of the Renyi divergence. -/

-- lemma meas_univ_add_mul_hellingerDiv_eq (ha_ne_zero : a ≠ 0) (ha_ne_one : a ≠ 1)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : hellingerDiv a μ ν ≠ ∞) :
--     ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν = ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν := by
--   rw_mod_cast [hellingerDiv_eq_integral_of_ne_top' ha_ne_zero ha_ne_one h,
--     ← ENNReal.ofReal_toReal (measure_ne_top ν .univ), EReal.coe_ennreal_ofReal,
--     max_eq_left ENNReal.toReal_nonneg, ← mul_sub, ← mul_assoc, mul_inv_cancel₀ _]
--   ring_nf
--   exact sub_ne_zero_of_ne ha_ne_one

-- lemma meas_univ_add_mul_hellingerDiv_zero_eq (ha : a = 0) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν = ν {x | 0 < (∂μ/∂ν) x} := by
--   simp only [ha, EReal.coe_zero, zero_sub, hellingerDiv_zero'', neg_mul, one_mul, rpow_zero,
--     integral_const, smul_eq_mul, mul_one]
--   rw [EReal.neg_sub, ← add_assoc, ← sub_eq_add_neg, EReal.sub_self, zero_add]
--   all_goals simp [measure_ne_top]

-- lemma meas_univ_add_mul_hellingerDiv_nonneg_of_le_one (ha_nonneg : 0 ≤ a) (ha : a ≤ 1)
--     (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     0 ≤ ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν := by
--   by_cases h_one : a = 1
--   · have : (1 - 1 : EReal) = 0 := EReal.sub_self (ne_of_beq_false rfl) (ne_of_beq_false rfl)
--     simp [h_one, add_zero, zero_mul, this, EReal.coe_ennreal_nonneg]
--   replace ha : a < 1 := ha.lt_of_ne h_one
--   calc
--     _ = (ν .univ) - (1 - ↑a) * hellingerDiv a μ ν := by
--       congr
--       rw [← neg_mul, EReal.neg_sub _ _, add_comm, sub_eq_add_neg] <;> simp
--     _ ≥ (ν .univ) - (1 - ↑a) * ((1 - a)⁻¹ * ν .univ) := by
--       simp_rw [sub_eq_add_neg]
--       gcongr
--       rw [EReal.neg_le_neg_iff]
--       gcongr
--       · norm_cast
--         simp only [le_add_neg_iff_add_le, zero_add, ha.le]
--       · exact hellingerDiv_le_of_lt_one ha_nonneg ha μ ν
--     _ = (ν .univ) - (ν .univ) := by
--       norm_cast
--       rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ (by linarith), EReal.coe_one, one_mul]
--     _ ≥ _ := by
--       rw [← ENNReal.toEReal_sub (measure_ne_top _ _) (le_refl _)]
--       simp

-- lemma meas_univ_add_mul_hellingerDiv_nonneg_of_one_lt (ha : 1 < a) (μ ν : Measure α)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     0 ≤ ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν := by
--   by_cases h_top : hellingerDiv a μ ν = ∞
--   · rw [h_top, EReal.mul_top_of_pos, EReal.add_top_of_ne_bot (EReal.coe_ennreal_ne_bot _)]
--     · exact OrderTop.le_top 0
--     · norm_cast
--       linarith
--   rw [meas_univ_add_mul_hellingerDiv_eq (by linarith) ha.ne' h_top]
--   simp only [ge_iff_le, EReal.coe_nonneg]
--   positivity

-- lemma meas_univ_add_mul_hellingerDiv_nonneg (ha_nonneg : 0 ≤ a) (μ ν : Measure α)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     0 ≤ ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν := by
--   by_cases h_le_one : a ≤ 1
--   · exact meas_univ_add_mul_hellingerDiv_nonneg_of_le_one ha_nonneg h_le_one μ ν
--   · exact meas_univ_add_mul_hellingerDiv_nonneg_of_one_lt
--       (lt_of_not_ge h_le_one) μ ν

-- lemma meas_univ_add_mul_hellingerDiv_eq_zero_iff (ha_ne_one : a ≠ 1)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--   ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν = 0 ↔ μ ⟂ₘ ν ∧ hellingerDiv a μ ν ≠ ∞ := by
--   by_cases h_top : hellingerDiv a μ ν = ∞
--   · simp only [h_top, ne_eq, not_true_eq_false, and_false, iff_false]
--     rcases (lt_or_gt_of_ne ha_ne_one) with ha | ha
--     · rw [EReal.mul_top_of_neg (by exact_mod_cast sub_neg.mpr ha), EReal.add_bot]
--       exact EReal.bot_ne_zero
--     · rw [EReal.mul_top_of_pos (by exact_mod_cast sub_pos.mpr ha),
--         EReal.add_top_of_ne_bot (EReal.coe_ennreal_ne_bot _)]
--       exact EReal.top_ne_zero
--   simp_rw [ne_eq, h_top, not_false_eq_true, and_true]
--   by_cases ha_zero : a = 0
--   · rw [meas_univ_add_mul_hellingerDiv_zero_eq ha_zero, ← Measure.rnDeriv_eq_zero,
--       EReal.coe_ennreal_eq_zero]
--     simp_rw [← not_le, ← ae_iff]
--     exact eventually_congr <| .of_forall <| fun _ ↦ nonpos_iff_eq_zero
--   rw [meas_univ_add_mul_hellingerDiv_eq ha_zero ha_ne_one h_top]
--   norm_cast
--   refine integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular ha_zero ?_
--   rw [← integrable_hellingerFun_iff_integrable_rpow ha_ne_one]
--   exact integrable_of_fDiv_ne_top h_top

-- lemma meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_lt_one (ha : a < 1)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν = 0 ↔ μ ⟂ₘ ν  := by
--   rw [meas_univ_add_mul_hellingerDiv_eq_zero_iff ha.ne, and_iff_left_iff_imp]
--   intro hμν
--   rw [hellingerDiv_of_mutuallySingular_of_lt_one ha hμν, ne_eq, EReal.mul_eq_top]
--   simp [measure_ne_top]

-- lemma meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_one_lt (ha : 1 < a)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν = 0 ↔ μ = 0 := by
--   rw [meas_univ_add_mul_hellingerDiv_eq_zero_iff ha.ne', hellingerDiv_ne_top_iff_of_one_le ha.le]
--   refine ⟨fun ⟨h, _, h'⟩ ↦ Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h' h,
--     fun h ↦ ?_⟩
--   simp only [h, Measure.MutuallySingular.zero_left, Measure.AbsolutelyContinuous.zero, and_true,
--     true_and]
--   apply Integrable.congr (show Integrable (fun _ ↦ hellingerFun a 0) ν from integrable_const _)
--   filter_upwards [ν.rnDeriv_zero] with x hx
--   simp [hx]

-- lemma toENNReal_meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_lt_one
--     (ha_nonneg : 0 ≤ a) (ha : a < 1) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     (↑(ν .univ) + (a - 1) * (hellingerDiv a μ ν)).toENNReal = 0 ↔ μ ⟂ₘ ν  := by
--   rw [← meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_lt_one ha, EReal.toENNReal_eq_zero_iff]
--   exact LE.le.le_iff_eq (meas_univ_add_mul_hellingerDiv_nonneg ha_nonneg μ ν)

-- lemma toENNReal_meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_one_lt (ha : 1 < a)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     (↑(ν .univ) + (a - 1) * (hellingerDiv a μ ν)).toENNReal = 0 ↔ μ = 0  := by
--   rw [← meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_one_lt ha (ν := ν),
--     EReal.toENNReal_eq_zero_iff]
--   exact LE.le.le_iff_eq (meas_univ_add_mul_hellingerDiv_nonneg (by positivity) μ ν)

-- lemma meas_univ_add_mul_hellingerDiv_ne_top_of_lt_one (ha : a < 1) [IsFiniteMeasure ν] :
--     ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν ≠ ∞ := by
--   apply EReal.add_ne_top
--   · simp [measure_ne_top]
--   · rw [ne_eq, EReal.mul_eq_top]
--     norm_cast
--     simp_rw [EReal.coe_ne_bot, EReal.coe_ne_top, sub_neg, sub_pos, ha, not_lt_of_gt ha,
--       hellingerDiv_ne_bot]
--     tauto

-- lemma meas_univ_add_mul_hellingerDiv_eq_top_iff_of_one_lt (ha : 1 < a)
--     [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     ↑(ν .univ) + (a - 1) * hellingerDiv a μ ν = ∞
--       ↔ ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∨ ¬ μ ≪ ν := by
--   rw [← integrable_hellingerFun_iff_integrable_rpow ha.ne',
--     ← hellingerDiv_eq_top_iff_of_one_le ha.le]
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · contrapose! h
--     refine EReal.add_ne_top ?_ ?_
--     · rw [ne_eq, EReal.coe_ennreal_eq_top_iff]
--       exact measure_ne_top ν .univ
--     · rw [ne_eq, EReal.mul_eq_top]
--       norm_cast
--       simp_rw [EReal.coe_ne_bot, EReal.coe_ne_top, sub_neg, sub_pos, ha, not_lt_of_gt ha,
--       hellingerDiv_ne_bot]
--       tauto
--   · rw [h, EReal.mul_top_of_pos (by exact_mod_cast sub_pos.mpr ha), EReal.add_top_of_ne_bot]
--     exact EReal.coe_ennreal_ne_bot _

-- end MeasUnivAddMulHellingerDiv

end ProbabilityTheory

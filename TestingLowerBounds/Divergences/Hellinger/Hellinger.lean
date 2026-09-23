/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.Hellinger.HellingerDivFun
import TestingLowerBounds.Divergences.KullbackLeibler.KullbackLeibler
import TestingLowerBounds.FDiv.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Hellinger divergence

## Main definitions

* `hellingerDiv a μ ν`: the Hellinger divergence of order `a`, the f-divergence for the divergence
  function `hellingerDivFun a`.

## Main statements

* `hellingerDiv_one`: the Hellinger divergence of order `1` is the Kullback-Leibler divergence.
* `hellingerDiv_of_nonpos`: `hellingerDiv a μ ν = 0` for `a ≤ 0`.
* `hellingerDiv_ne_top_of_lt_one`, `hellingerDiv_eq_top_iff`: finiteness of the divergence.
* `hellingerDiv_comp_le_compProd`, `hellingerDiv_comp_right_le`: data-processing inequalities.

-/

open Real MeasureTheory Filter MeasurableSpace InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

/-- Hellinger divergence of order `a`, the f-divergence for the function `hellingerDivFun a`.
For `a = 1` the Hellinger divergence coincides with the Kullback-Leibler divergence.
For `a ≤ 0` the divergence function is `0`, hence `hellingerDiv a μ ν = 0`.
In particular `hellingerDiv 0 μ ν = 0`: the value `ν {x | (∂μ/∂ν) x = 0}` that is sometimes used as
Hellinger divergence of order `0` in the literature is not the f-divergence of a `DivFunction`,
since such a function has to be continuous at `0`. The Rényi divergence of order `0` is defined
separately (see `renyiDiv`). -/
noncomputable def hellingerDiv (a : ℝ) (μ ν : Measure α) : ℝ≥0∞ := fDiv (hellingerDivFun a) μ ν

@[simp] lemma hellingerDiv_of_nonpos (ha : a ≤ 0) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν = 0 := by
  rw [hellingerDiv, hellingerDivFun_of_nonpos ha, fDiv_zero]

lemma hellingerDiv_zero [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv 0 μ ν = 0 := by simp

@[simp] lemma hellingerDiv_one (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv 1 μ ν = klDiv μ ν := by
  rw [hellingerDiv, hellingerDivFun_one, klDiv_eq_fDiv]

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

lemma toReal_hellingerDiv_eq_integral_of_integrable_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1)
    (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) (hμν : μ ≪ ν) :
    (hellingerDiv a μ ν).toReal
      = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * (μ .univ).toReal := by
  simp [hellingerDiv, hellingerDivFun_of_pos_of_ne_one ha_pos ha_ne]
  rw [toReal_fDiv_ofReal_eq_integral_add_of_ac (fun x hx ↦ hellingerFun_nonneg ha_pos.le hx)
    (continuous_hellingerFun ha_pos).continuousWithinAt _ hμν]
  swap; · rwa [integrable_hellingerFun_iff_integrable_rpow ha_ne]
  rw [integral_hellingerFun_of_pos_of_ne_one_of_integrable_of_ac ha_pos ha_ne h_int hμν]

lemma toReal_hellingerDiv_eq_integral_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_lt : a < 1) :
    (hellingerDiv a μ ν).toReal
      = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * (μ .univ).toReal := by
  simp [hellingerDiv, hellingerDivFun_of_pos_of_ne_one ha_pos ha_lt.ne]
  rw [toReal_fDiv_ofReal_eq_integral_add', integral_hellingerFun_of_pos_of_lt_one ha_pos ha_lt,
    ← hellingerDivFun_of_pos_of_ne_one ha_pos ha_lt.ne,
    derivAtTop_hellingerDivFun_of_lt_one ha_pos ha_lt, ENNReal.toReal_ofReal]
  rotate_left
  · refine mul_nonneg ha_pos.le ?_
    simp [ha_lt.le]
  · exact fun x hx ↦ hellingerFun_nonneg ha_pos.le hx
  · exact (continuous_hellingerFun ha_pos).continuousWithinAt
  · exact integrable_hellingerFun_rnDeriv_of_lt_one ha_pos.le ha_lt
  · rw [← hellingerDivFun_of_pos_of_ne_one ha_pos ha_lt.ne,
      derivAtTop_hellingerDivFun_of_lt_one ha_pos ha_lt]
    simp
  rw [add_assoc, add_assoc, add_assoc]
  congr 2
  rw [mul_comm a, ← mul_add]
  congr 1
  conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm, Measure.coe_add, Pi.add_apply,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ, add_left_inj]
  rw [integral_toReal]
  · exact (μ.measurable_rnDeriv ν).aemeasurable
  · exact μ.rnDeriv_lt_top ν

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
  rcases le_or_gt a 0 with (ha0 | ha0)
  · simp [ha0]
  rw [hellingerDiv_eq_integral_of_lt_one ha0 ha]
  simp

lemma lintegral_hellingerDivFun_eq_top_of_not_integrable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_one : a ≠ 1)
    (h : ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) :
    ∫⁻ x, hellingerDivFun a ((∂μ/∂ν) x) ∂ν = ∞ := by
  rw [← integrable_hellingerFun_iff_integrable_rpow ha_one] at h
  simp [hellingerDivFun, (not_le.mpr ha_pos), ha_one]
  exact DivFunction.lintegral_ofReal_eq_top_of_not_integrable
    (fun _ hx ↦ hellingerFun_nonneg ha_pos.le hx) h

lemma hellingerDiv_of_not_integrable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha : 0 ≤ a)
    (h : ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    hellingerDiv a μ ν = ∞ := by
  by_cases ha_zero : a = 0
  · simp only [ha_zero, le_refl, hellingerDiv_of_nonpos, ENNReal.zero_ne_top]
    refine h ?_
    simp only [ha_zero, hellingerFun_zero]
    refine integrable_of_le_of_le (g₁ := fun _ ↦ 0) (g₂ := fun _ ↦ 1) ?_ ?_ ?_
      (integrable_const _) (integrable_const _)
    · refine Measurable.aestronglyMeasurable ?_
      refine Measurable.ite ?_ measurable_const measurable_const
      exact (μ.measurable_rnDeriv ν).ennreal_toReal (measurableSet_singleton 0)
    · refine ae_of_all _ fun x ↦ ?_
      simp only
      split_ifs <;> simp
    · refine ae_of_all _ fun x ↦ ?_
      simp only
      split_ifs <;> simp
  have ha_pos : 0 < a := ha.lt_of_ne (Ne.symm ha_zero)
  by_cases ha_one : a = 1
  · simp only [ha_one, hellingerDiv_one]
    rw [klDiv_eq_top_iff]
    intro hμν
    rwa [ha_one, integrable_hellingerFun_one_iff hμν] at h
  simp [hellingerDiv, hellingerDivFun, (not_le.mpr ha_pos), ha_one]
  exact fDiv_ofReal_of_not_integrable (fun _ hx ↦ hellingerFun_nonneg ha_pos.le hx) h

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
  push Not
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
  push Not
  rfl

lemma hellingerDiv_eq_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν = ∞
      ↔ ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∨ ¬ μ ≪ ν := by
  rw [hellingerDiv_eq_top_iff_of_one_le ha.le, ← integrable_hellingerFun_iff_integrable_rpow ha.ne']
  rw [hellingerDivFun_of_pos_of_ne_one (zero_lt_one.trans ha) ha.ne',
    DivFunction.lintegral_ofReal_eq_top_iff_not_integrable_of_continuous
      (fun _ hx ↦ hellingerFun_nonneg (zero_lt_one.trans ha).le hx)]
  exact (continuous_hellingerFun (zero_lt_one.trans ha)).continuousWithinAt

lemma hellingerDiv_ne_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν ≠ ∞
      ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∧ μ ≪ ν := by
  rw [ne_eq, hellingerDiv_eq_top_iff_of_one_lt ha]
  tauto

lemma hellingerDiv_eq_ofReal_integral_of_integrable_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (h_int : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν)
    (hμν : μ ≪ ν) :
    hellingerDiv a μ ν = ENNReal.ofReal (∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν) := by
  rw [hellingerDiv, hellingerDivFun_of_pos ha_pos]
  exact fDiv_ofReal_eq_integral_of_ac (fun _ hx ↦ hellingerFun_nonneg ha_pos.le hx)
    (continuous_hellingerFun ha_pos).continuousWithinAt h_int hμν

lemma lintegral_hellingerDivFun_ne_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1) :
    ∫⁻ x, hellingerDivFun a ((∂μ/∂ν) x) ∂ν ≠ ∞
      ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν := by
  rw [← integrable_hellingerFun_iff_integrable_rpow ha_ne,
    hellingerDivFun_of_pos_of_ne_one ha_pos ha_ne,
    DivFunction.lintegral_ofReal_ne_top_iff_integrable_of_continuous
      (fun _ hx ↦ hellingerFun_nonneg ha_pos.le hx) (continuous_hellingerFun ha_pos).continuousWithinAt]

lemma toReal_hellingerDiv_eq_integral_of_one_lt_of_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha : 1 < a) (h : hellingerDiv a μ ν ≠ ∞) :
    (hellingerDiv a μ ν).toReal
      = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * (μ .univ).toReal := by
  rw [hellingerDiv_ne_top_iff_of_one_lt ha] at h
  exact toReal_hellingerDiv_eq_integral_of_integrable_of_ac (zero_lt_one.trans ha) ha.ne' h.1 h.2

/-- Integral form of the Hellinger divergence, for `a ∈ (0, 1) ∪ (1, ∞)` and a finite divergence. -/
lemma toReal_hellingerDiv_eq_integral_of_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1) (h : hellingerDiv a μ ν ≠ ∞) :
    (hellingerDiv a μ ν).toReal
      = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * (μ .univ).toReal := by
  rcases lt_or_gt_of_ne ha_ne with ha_lt | ha_lt
  · exact toReal_hellingerDiv_eq_integral_of_lt_one ha_pos ha_lt
  · exact toReal_hellingerDiv_eq_integral_of_one_lt_of_ne_top ha_lt h

lemma hellingerDiv_of_mutuallySingular_of_one_le (ha : 1 ≤ a) [hμ : NeZero μ]
    [SigmaFinite μ] [IsFiniteMeasure ν] (hμν : μ ⟂ₘ ν) :
    hellingerDiv a μ ν = ∞ := by
  have ha_pos : 0 < a := by positivity
  simp [not_le.mpr ha_pos, hellingerDiv, fDiv_of_mutuallySingular hμν, not_lt.mpr ha,
    hμ.out]

lemma hellingerDiv_of_mutuallySingular_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    [SigmaFinite μ] [IsFiniteMeasure ν] (hμν : μ ⟂ₘ ν) :
    hellingerDiv a μ ν = ν Set.univ + ENNReal.ofReal (a * (1 - a)⁻¹) * μ Set.univ := by
  rw [hellingerDiv, fDiv_of_mutuallySingular hμν, derivAtTop_hellingerDivFun_of_lt_one ha_pos ha,
    hellingerDivFun_apply_zero, ite_eq_right (not_le.mpr ha_pos), one_mul]

lemma toReal_hellingerDiv_of_mutuallySingular_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ⟂ₘ ν) :
    (hellingerDiv a μ ν).toReal = (ν .univ).toReal + (a * (1 - a)⁻¹) * (μ .univ).toReal := by
  rw [hellingerDiv_of_mutuallySingular_of_lt_one ha_pos ha hμν]
  rw [ENNReal.toReal_add (measure_ne_top _ _), ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  · exact mul_nonneg ha_pos.le (inv_nonneg.mpr (sub_nonneg_of_le ha.le))
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

end HellingerEq

lemma toReal_hellingerDiv_symm (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (1 - a) * (hellingerDiv a μ ν).toReal = a * (hellingerDiv (1 - a) ν μ).toReal := by
  rw [toReal_hellingerDiv_eq_integral_of_lt_one ha_pos ha,
    toReal_hellingerDiv_eq_integral_of_lt_one]
  rotate_left
  · linarith
  · linarith
  simp only [sub_sub_cancel_left, sub_sub_cancel]
  rw [integral_rpow_rnDeriv ha_pos ha.ne]
  rw [inv_neg, mul_add, mul_add, mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    ← mul_assoc, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀, mul_inv_cancel₀, one_mul, one_mul,
    add_assoc, add_comm _ (a * (μ Set.univ).toReal), ← add_assoc]
  rotate_left
  · exact ha_pos.ne'
  · linarith
  congr 3
  rw [← neg_sub, neg_mul, mul_inv_cancel₀, mul_neg, mul_inv_cancel₀ ha_pos.ne']
  linarith

lemma hellingerDiv_symm (ha_pos : 0 < a) (ha : a < 1) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal.ofReal (1 - a) * hellingerDiv a μ ν = ENNReal.ofReal a * hellingerDiv (1 - a) ν μ := by
  rw [← ENNReal.toReal_eq_toReal_iff', ENNReal.toReal_mul, ENNReal.toReal_mul]
  rotate_left
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top <| hellingerDiv_ne_top_of_lt_one ha μ ν
  · refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top <| hellingerDiv_ne_top_of_lt_one ?_ ν μ
    linarith
  rw [ENNReal.toReal_ofReal ha_pos.le, ENNReal.toReal_ofReal (by linarith)]
  exact toReal_hellingerDiv_symm ha_pos ha

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

section MeasUnivAddMulHellingerDiv

/-! In this section there are results about the expression `ν(α) + (a - 1) * Hₐ(μ, ν)`,
which appears in the definition of the Renyi divergence. -/

--Maybe we could write something like this for the conditional case? Would it be useful?
lemma hellingerDiv_le_of_lt_one (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν ≤ ν Set.univ + ENNReal.ofReal (a * (1 - a)⁻¹) * μ Set.univ := by
  by_cases h_zero : a ≤ 0
  · simp [h_zero]
  refine fDiv_le_zero_add_top.trans_eq ?_
  simp [h_zero, ha]

lemma mul_hellingerDiv_add_meas_eq_integral_of_integrable_of_ac
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1)
    (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) (hμν : μ ≪ ν) :
    (1 - a) * (ν .univ).toReal + a * (μ .univ).toReal + (a - 1) * (hellingerDiv a μ ν).toReal
      = ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν := by
  rw [toReal_hellingerDiv_eq_integral_of_integrable_of_ac ha_pos ha_ne h_int hμν]
  rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀, one_mul,
    add_assoc, ← neg_sub 1 a, neg_mul, neg_mul, mul_inv_cancel₀]
  rotate_left
  · rw [sub_ne_zero]; exact ha_ne.symm
  · rw [sub_ne_zero]; exact ha_ne
  ring

lemma mul_hellingerDiv_add_meas_eq_integral_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_lt : a < 1) :
    (1 - a) * (ν .univ).toReal + a * (μ .univ).toReal + (a - 1) * (hellingerDiv a μ ν).toReal
      = ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν := by
  rw [toReal_hellingerDiv_eq_integral_of_lt_one ha_pos ha_lt]
  rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀, one_mul,
    add_assoc, ← neg_sub 1 a, neg_mul, neg_mul, mul_inv_cancel₀]
  rotate_left
  · rw [sub_ne_zero]; exact ha_lt.ne'
  · rw [sub_ne_zero]; exact ha_lt.ne
  ring

lemma mul_hellingerDiv_le_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_lt : a < 1) :
    (1 - a) * (hellingerDiv a μ ν).toReal ≤ (1 - a) * (ν .univ).toReal + a * (μ .univ).toReal := by
  rw [← sub_nonneg, sub_eq_add_neg, ← neg_mul, neg_sub,
    mul_hellingerDiv_add_meas_eq_integral_of_lt_one ha_pos ha_lt]
  exact integral_nonneg fun x ↦ by positivity

lemma toReal_hellingerDiv_eq_add_measure_univ_iff_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (hellingerDiv a μ ν).toReal = (ν .univ).toReal + (a * (1 - a)⁻¹) * (μ .univ).toReal
      ↔ μ ⟂ₘ ν := by
  refine ⟨fun h ↦ ?_, toReal_hellingerDiv_of_mutuallySingular_of_lt_one ha_pos ha⟩
  rw [toReal_hellingerDiv_eq_integral_of_lt_one ha_pos ha] at h
  rw [← integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular (a := a) ha_pos.ne']
  swap; · exact integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha
  rw [mul_comm a, add_assoc, add_comm, add_eq_left, mul_eq_zero, inv_eq_zero,
    sub_eq_zero] at h
  simpa [ha.ne] using h

lemma toReal_hellingerDiv_ne_add_measure_univ_of_one_lt (ha_lt : 1 < a)
    [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_top : hellingerDiv a μ ν ≠ ∞) :
    (hellingerDiv a μ ν).toReal ≠ (ν .univ).toReal + (a * (1 - a)⁻¹) * (μ .univ).toReal := by
  have h : ¬ μ ⟂ₘ ν := fun h ↦ h_top (hellingerDiv_of_mutuallySingular_of_one_le ha_lt.le h)
  rw [hellingerDiv_ne_top_iff_of_one_lt ha_lt] at h_top
  rw [toReal_hellingerDiv_eq_integral_of_integrable_of_ac (zero_lt_one.trans ha_lt)
    ha_lt.ne' h_top.1 h_top.2]
  rw [mul_comm a, add_assoc, add_comm, ne_eq, add_eq_left, mul_eq_zero, inv_eq_zero,
    sub_eq_zero]
  simp only [ha_lt.ne', false_or]
  rwa [integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular (a := a) (zero_lt_one.trans ha_lt).ne'
    h_top.1]

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
    have hν_eq : ν .univ = ENNReal.ofReal (ν .univ).toReal := by
      rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hμ_eq : μ .univ = ENNReal.ofReal (μ .univ).toReal := by
      rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    conv_lhs => rw [hν_eq, hμ_eq]
    rw [← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
    · positivity
    · refine mul_nonneg (mul_nonneg ha_pos.le ?_) ENNReal.toReal_nonneg
      simp [ha.le]
    · refine mul_nonneg ha_pos.le ?_
      simp [ha.le]
  rw [h_eq, ENNReal.ofReal_eq_ofReal_iff, add_assoc, mul_comm a, add_eq_right, mul_eq_zero,
    inv_eq_zero, sub_eq_zero] at h
  · simpa [ha.ne] using h
  · refine (integral_hellingerFun_rnDeriv_nonneg ha_pos ha (μ := μ) (ν := ν)).trans ?_
    refine add_le_add le_rfl ?_
    gcongr
    rw [Measure.integral_toReal_rnDeriv']
    exact sub_le_self _ ENNReal.toReal_nonneg
  · refine add_nonneg (by positivity) (mul_nonneg (mul_nonneg ha_pos.le ?_) (by positivity))
    simp [ha.le]

end MeasUnivAddMulHellingerDiv

end ProbabilityTheory

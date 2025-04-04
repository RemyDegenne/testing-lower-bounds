/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.Order.CompletePartialOrder
import TestingLowerBounds.CurvatureMeasure
import TestingLowerBounds.Divergences.StatInfo.StatInfo
import TestingLowerBounds.FDiv.Measurable

/-!
# fDiv and StatInfo

-/

open MeasureTheory Set ProbabilityTheory.DivFunction

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {p : ℝ≥0∞} {π : Measure Bool} {f : DivFunction} {β γ x t : ℝ}

noncomputable
def statInfoDivFun (β γ : ℝ) : DivFunction :=
  DivFunction.ofReal
    (statInfoFun β γ) ((convexOn_statInfoFun β γ).subset (subset_univ _) (convex_Ioi 0))
    statInfoFun_apply_one

lemma measurable_statInfoDivFun :
    Measurable (Function.uncurry fun (a : ℝ × ℝ) x ↦ statInfoDivFun a.1 a.2 ((∂μ/∂ν) x)) := by
  have h_meas := stronglyMeasurable_statInfoFun.measurable.comp
    (f := fun ((a, b), x) ↦ ((a, b), ((∂μ/∂ν) x).toReal)) (measurable_fst.prod_mk (by fun_prop))
  unfold statInfoDivFun
  -- convert h_meas
  sorry

section derivAtTop

lemma derivAtTop_statInfoDivFun_of_nonneg_of_le (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    (statInfoDivFun β γ).derivAtTop = 0 := by
  rw [statInfoDivFun, derivAtTop_ofReal]
  sorry

lemma derivAtTop_statInfoDivFun_of_nonneg_of_gt (hβ : 0 ≤ β) (hγ : γ > β) :
    (statInfoDivFun β γ).derivAtTop = ENNReal.ofReal β := by
  sorry

lemma derivAtTop_statInfoDivFun_of_nonpos_of_le (hβ : β ≤ 0) (hγ : γ ≤ β) :
    (statInfoDivFun β γ).derivAtTop = ENNReal.ofReal (-β) := by
  sorry

lemma derivAtTop_statInfoDivFun_of_nonpos_of_gt (hβ : β ≤ 0) (hγ : γ > β) :
    (statInfoDivFun β γ).derivAtTop = 0 := by
  sorry

lemma derivAtTop_statInfoDivFun_eq :
    (statInfoDivFun β γ).derivAtTop
      = if 0 ≤ β then (if γ ≤ β then 0 else ENNReal.ofReal β)
        else if γ ≤ β then ENNReal.ofReal (-β) else 0 := by
  by_cases hβ : 0 ≤ β <;> by_cases hγ : γ ≤ β <;> simp [derivAtTop_statInfoDivFun_of_nonneg_of_le,
    derivAtTop_statInfoDivFun_of_nonneg_of_gt, derivAtTop_statInfoDivFun_of_nonpos_of_le,
    derivAtTop_statInfoDivFun_of_nonpos_of_gt, hβ, hγ, lt_of_not_le, le_of_lt (lt_of_not_le _)]

lemma derivAtTop_statInfoDivFun_ne_top (β γ : ℝ) :
    (statInfoDivFun β γ).derivAtTop ≠ ∞ := by
  rcases le_total 0 β with (hβ | hβ) <;> rcases le_or_lt γ β with (hγ | hγ) <;>
    simp [derivAtTop_statInfoDivFun_of_nonneg_of_le, derivAtTop_statInfoDivFun_of_nonneg_of_gt,
      derivAtTop_statInfoDivFun_of_nonpos_of_le, derivAtTop_statInfoDivFun_of_nonpos_of_gt, hβ, hγ]

end derivAtTop

end ProbabilityTheory

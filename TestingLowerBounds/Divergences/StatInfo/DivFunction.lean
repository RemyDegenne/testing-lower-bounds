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
def statInfoDivFun (β γ : ℝ) : DivFunction := DivFunction.ofConvexOn
  (statInfoFun β γ) ((convexOn_statInfoFun β γ).subset (subset_univ _) (convex_Ioi 0))

lemma measurable_statInfoDivFun :
    Measurable (Function.uncurry fun (a : ℝ × ℝ) x ↦ statInfoDivFun a.1 a.2 ((∂μ/∂ν) x)) := by
  sorry

section derivAtTop

lemma derivAtTop_statInfoDivFun_of_nonneg_of_le (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    (statInfoDivFun β γ).derivAtTop = 0 := by
  rw [statInfoDivFun, derivAtTop_ofConvexOn]
  rw [← derivAtTop_zero]
  refine derivAtTop_congr ?_
  rw [EventuallyEq, eventually_atTop]
  refine ⟨1, fun x hx ↦ ?_⟩
  rw [statInfoFun_of_le hγ]
  simp only [Pi.zero_apply, max_eq_left_iff, tsub_le_iff_right, zero_add]
  refine hγ.trans ?_
  conv_lhs => rw [← mul_one β]
  gcongr

lemma derivAtTop_statInfoFun_of_nonneg_of_gt (hβ : 0 ≤ β) (hγ : γ > β) :
    derivAtTop (fun x ↦ statInfoFun β γ x) = β := by
  rcases eq_or_lt_of_le hβ with (rfl | hβ)
  · simp
  have : (β : EReal) = derivAtTop (fun x ↦ β * x - γ) := by
    rw [derivAtTop_sub_const]
    swap; · exact (ConvexOn.const_mul_id _).subset (subset_univ _) (convex_Ici _)
    change _ = derivAtTop (fun x ↦ β * x)
    rw [derivAtTop_const_mul _ hβ.ne']
    swap; · exact convexOn_id (convex_Ici _)
    simp only [derivAtTop_id', mul_one]
  rw [this]
  refine derivAtTop_congr ?_
  rw [EventuallyEq, eventually_atTop]
  refine ⟨γ / β, fun x hx ↦ ?_⟩
  rw [statInfoFun_of_pos_of_gt_of_ge hβ hγ hx]

lemma derivAtTop_statInfoFun_of_nonpos_of_le (hβ : β ≤ 0) (hγ : γ ≤ β) :
    derivAtTop (fun x ↦ statInfoFun β γ x) = -β := by
  rcases eq_or_lt_of_le hβ with (rfl | hβ)
  · simp
  have : -(β : EReal) = derivAtTop (fun x ↦ γ - β * x) := by
    simp_rw [sub_eq_add_neg, ← neg_mul]
    rw [derivAtTop_const_add]
    swap
    · change ConvexOn ℝ (Ici _) (fun x ↦ (-β) • x)
      refine (convexOn_id (convex_Ici _)).smul ?_
      simp [hβ.le]
    rw [derivAtTop_const_mul]
    · simp
    · exact convexOn_id (convex_Ici _)
    · simp only [ne_eq, neg_eq_zero, hβ.ne, not_false_eq_true]
  rw [this]
  refine derivAtTop_congr ?_
  rw [EventuallyEq, eventually_atTop]
  refine ⟨γ / β, fun x hx ↦ ?_⟩
  rw [statInfoFun_of_neg_of_le_of_ge hβ hγ hx]

lemma derivAtTop_statInfoFun_of_nonpos_of_gt (hβ : β ≤ 0) (hγ : γ > β) :
    derivAtTop (fun x ↦ statInfoFun β γ x) = 0 := by
  rcases eq_or_lt_of_le hβ with (rfl | hβ)
  · simp
  rw [← derivAtTop_zero]
  refine derivAtTop_congr ?_
  rw [EventuallyEq, eventually_atTop]
  refine ⟨γ / β, fun x hx ↦ ?_⟩
  rw [statInfoFun_of_gt hγ]
  simp only [Pi.zero_apply, max_eq_left_iff, tsub_le_iff_right, zero_add]
  rwa [ge_iff_le, div_le_iff_of_neg hβ, mul_comm] at hx

lemma derivAtTop_statInfoFun_eq :
    derivAtTop (fun x ↦ statInfoFun β γ x)
      = if 0 ≤ β then (if γ ≤ β then 0 else β) else if γ ≤ β then -β else 0 := by
  by_cases hβ : 0 ≤ β <;> by_cases hγ : γ ≤ β <;> simp [derivAtTop_statInfoFun_of_nonneg_of_le,
    derivAtTop_statInfoFun_of_nonneg_of_gt, derivAtTop_statInfoFun_of_nonpos_of_le,
    derivAtTop_statInfoFun_of_nonpos_of_gt, hβ, hγ, lt_of_not_le, le_of_lt (lt_of_not_le _)]

lemma derivAtTop_statInfoFun_ne_top (β γ : ℝ) : derivAtTop (fun x ↦ statInfoFun β γ x) ≠ ⊤ := by
  rcases le_total 0 β with (hβ | hβ) <;> rcases le_or_lt γ β with (hγ | hγ) <;>
    simp [derivAtTop_statInfoFun_of_nonneg_of_le, derivAtTop_statInfoFun_of_nonneg_of_gt,
      derivAtTop_statInfoFun_of_nonpos_of_le, derivAtTop_statInfoFun_of_nonpos_of_gt, hβ, hγ]

lemma derivAtTop_statInfoFun_nonneg (β γ : ℝ) : 0 ≤ derivAtTop (fun x ↦ statInfoFun β γ x) := by
  rcases le_total 0 β with (hβ | hβ) <;> rcases le_or_lt γ β with (hγ | hγ) <;>
    simp [derivAtTop_statInfoFun_of_nonneg_of_le, derivAtTop_statInfoFun_of_nonneg_of_gt,
      ← EReal.coe_neg, derivAtTop_statInfoFun_of_nonpos_of_le,
      derivAtTop_statInfoFun_of_nonpos_of_gt, hβ, hγ]

end derivAtTop

end ProbabilityTheory

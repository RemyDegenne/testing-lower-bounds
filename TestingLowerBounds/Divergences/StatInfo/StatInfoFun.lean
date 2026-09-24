/-
Copyright (c) 2024 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Regular
public import TestingLowerBounds.DerivAtTop

/-! # The functions `statInfoFun β γ`

Properties of the functions `statInfoFun β γ : ℝ → ℝ`, the building blocks of the integral
representation of f-divergences in terms of statistical informations.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

open scoped ENNReal NNReal Interval

namespace ProbabilityTheory

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳} {f : ℝ → ℝ} {β γ x t : ℝ}

/- To play with this function go to https://www.geogebra.org/calculator/jaymzqtm,
there the notation is: b for β, c for γ, X for x.
h is statInfoFun seen as a function of x, f is statInfoFun seen as a function of γ.
-/
/-- The hockey-stick function, it is related to the statistical information divergence. -/
noncomputable
def statInfoFun (β γ x : ℝ) : ℝ := if γ ≤ β then max 0 (γ - β * x) else max 0 (β * x - γ)

lemma statInfoFun_nonneg (β γ x : ℝ) : 0 ≤ statInfoFun β γ x := by
  simp_rw [statInfoFun]
  split_ifs <;> simp

@[simp]
lemma statInfoFun_one : statInfoFun 1 γ x = if γ ≤ 1 then max 0 (γ - x) else max 0 (x - γ) := by
  simp_rw [statInfoFun, one_mul]

@[simp]
lemma statInfoFun_zero : statInfoFun 0 γ x = 0 := by simp_all [statInfoFun, le_of_lt]

@[simp]
lemma statInfoFun_zero' : statInfoFun 0 γ = 0 := by ext; simp_all [statInfoFun, le_of_lt]

lemma const_mul_statInfoFun {a : ℝ} (ha : 0 ≤ a) :
    a * statInfoFun β γ x = statInfoFun (a * β) (a * γ) x := by
  simp_rw [statInfoFun, mul_ite, mul_max_of_nonneg _ _ ha, mul_sub, mul_zero, mul_assoc]
  rcases lt_or_eq_of_le ha with (ha | rfl)
  · simp_rw [mul_le_mul_iff_right₀ ha]
  · simp

lemma statInfoFun_neg_neg (h : β ≠ γ) : statInfoFun (-β) (-γ) = statInfoFun β γ := by
  ext
  rcases lt_or_gt_of_ne h with (hγβ | hγβ)
    <;> simp [statInfoFun, sub_eq_add_neg, hγβ.le, hγβ.not_ge, add_comm]

section Measurability

lemma measurable_statInfoFun : Measurable statInfoFun.uncurry.uncurry := by
  change Measurable (fun (p : (ℝ × ℝ) × ℝ) ↦ if p.1.2 ≤ p.1.1 then max 0 (p.1.2 - p.1.1 * p.2)
    else max 0 (p.1.1 * p.2 - p.1.2))
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) (by fun_prop)
  · fun_prop
  · fun_prop

lemma stronglyMeasurable_statInfoFun3 : StronglyMeasurable (statInfoFun β γ) := by
  change StronglyMeasurable (statInfoFun.uncurry.uncurry ∘ (fun (x : ℝ) ↦ ((β, γ), x)))
  refine measurable_statInfoFun.comp (by fun_prop) |>.stronglyMeasurable

end Measurability

section statInfoFun_x
-- Lemmas useful when we want to consider `statInfoFun` as a function of `x`

lemma statInfoFun_of_le (h : γ ≤ β) : statInfoFun β γ x = max 0 (γ - β * x) := ite_eq_left h

lemma statInfoFun_of_le' (h : γ ≤ β) : statInfoFun β γ = fun x ↦ max 0 (γ - β * x) := by
  ext; exact statInfoFun_of_le h

lemma statInfoFun_of_gt (h : γ > β) : statInfoFun β γ x = max 0 (β * x - γ) := ite_eq_right h.not_ge

lemma statInfoFun_of_gt' (h : γ > β) : statInfoFun β γ = fun x ↦ max 0 (β * x - γ) := by
  ext; exact statInfoFun_of_gt h

lemma statInfoFun_of_pos_of_gt_of_ge (hβ : 0 < β) (hγ : γ > β) (hx : x ≥ γ / β) :
    statInfoFun β γ x = β * x - γ :=
  statInfoFun_of_gt hγ ▸ max_eq_right_iff.mpr <| sub_nonneg.mpr <| (div_le_iff₀' hβ).mp hx

lemma statInfoFun_of_neg_of_le_of_ge (hβ : β < 0) (hγ : γ ≤ β) (hx : x ≥ γ / β) :
    statInfoFun β γ x = γ - β * x :=
  statInfoFun_of_le hγ ▸ max_eq_right_iff.mpr <| sub_nonneg.mpr <| (div_le_iff_of_neg' hβ).mp hx

@[simp]
lemma statInfoFun_apply_one : statInfoFun β γ 1 = 0 := by
  unfold statInfoFun
  split_ifs with h
  · simp [h]
  · simp [(not_le.mp h).le]

lemma convexOn_statInfoFun (β γ : ℝ) : ConvexOn ℝ univ (statInfoFun β γ) := by
  unfold statInfoFun
  by_cases h : γ ≤ β <;>
  · simp only [h, ↓reduceIte]
    refine (convexOn_const 0 convex_univ).sup ⟨convex_univ, fun x _ y _ a b _ _ hab ↦ le_of_eq ?_⟩
    dsimp
    have hγ : γ = a * γ + b * γ := by rw [← add_mul, hab, one_mul]
    linarith

lemma continuous_statInfoFun : Continuous (statInfoFun β γ) := by
  rcases le_or_gt γ β with hγ | hγ
  · rw [statInfoFun_of_le' hγ]
    exact continuous_const.max (continuous_const.sub (continuous_const.mul continuous_id))
  · rw [statInfoFun_of_gt' hγ]
    exact continuous_const.max ((continuous_const.mul continuous_id).sub continuous_const)

lemma continuousWithinAt_statInfoFun_zero :
    ContinuousWithinAt (statInfoFun β γ) (Ioi 0) 0 :=
  continuous_statInfoFun.continuousWithinAt

section derivAtTop

lemma derivAtTop_statInfoFun_of_nonneg_of_le (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    derivAtTop (fun x ↦ statInfoFun β γ x) = 0 := by
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
  rwa [div_le_iff_of_neg hβ, mul_comm] at hx

lemma derivAtTop_statInfoFun_ne_top (β γ : ℝ) : derivAtTop (fun x ↦ statInfoFun β γ x) ≠ ⊤ := by
  rcases le_total 0 β with (hβ | hβ) <;> rcases le_or_gt γ β with (hγ | hγ) <;>
    simp [derivAtTop_statInfoFun_of_nonneg_of_le, derivAtTop_statInfoFun_of_nonneg_of_gt,
      derivAtTop_statInfoFun_of_nonpos_of_le, derivAtTop_statInfoFun_of_nonpos_of_gt, hβ, hγ]

end derivAtTop

end statInfoFun_x

section statInfoFun_γ

lemma statInfoFun_of_nonneg_of_right_le_one (hβ : 0 ≤ β) (hx : x ≤ 1) :
    statInfoFun β γ x = (Ioc (β * x) β).indicator (fun y ↦ y - β * x) γ := by
  by_cases hγβ : γ ≤ β
  · by_cases hβxγ : β * x < γ
    · simp [statInfoFun, indicator, hβxγ, hβxγ.le]
    · simp [statInfoFun, hγβ, hβxγ, (le_of_not_gt hβxγ)]
  · simp only [statInfoFun, hγβ, ↓reduceIte, indicator, mem_Ioc, and_false, max_eq_left_iff,
      tsub_le_iff_right, zero_add]
    exact (mul_le_of_le_one_right hβ hx).trans (le_of_not_ge hγβ)

lemma statInfoFun_of_nonneg_of_one_le_right (hβ : 0 ≤ β) (hx : 1 ≤ x) :
    statInfoFun β γ x = (Ioc β (β * x)).indicator (fun y ↦ β * x - y) γ := by
  by_cases hγβ : γ ≤ β
  · simp [statInfoFun, hγβ, indicator, hγβ.trans (le_mul_of_one_le_right hβ hx), hγβ.not_gt]
  · by_cases hγβx : γ ≤ β * x
    · simp [statInfoFun, hγβ, hγβx, lt_of_not_ge hγβ]
    · simp [statInfoFun, hγβ, hγβx, le_of_not_ge hγβx]

lemma statInfoFun_of_one_of_one_le_right (h : 1 ≤ x) :
    statInfoFun 1 γ x = (Ioc 1 x).indicator (fun y ↦ x - y) γ := by
  convert statInfoFun_of_nonneg_of_one_le_right _ h <;> simp

lemma statInfoFun_of_one_of_right_le_one (h : x ≤ 1) :
    statInfoFun 1 γ x = (Ioc x 1).indicator (fun y ↦ y - x) γ := by
  convert statInfoFun_of_nonneg_of_right_le_one _ h <;> simp

end statInfoFun_γ

end ProbabilityTheory

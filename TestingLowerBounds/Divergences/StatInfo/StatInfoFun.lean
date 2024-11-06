/-
Copyright (c) 2024 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Regular
import TestingLowerBounds.DerivAtTop

open MeasureTheory Set Filter Topology StieltjesFunction

open scoped ENNReal NNReal

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
  · simp_rw [mul_le_mul_left ha]
  · simp

lemma statInfoFun_neg_neg (h : β ≠ γ) : statInfoFun (-β) (-γ) = statInfoFun β γ := by
  ext
  rcases lt_or_gt_of_ne h with (hγβ | hγβ)
    <;> simp [statInfoFun, sub_eq_add_neg, hγβ.le, hγβ.not_le, add_comm]

--TODO: for now I will leave the continuity assumption in some lemmas, it should be derived from the convexity but the lemma is not yet in mathlib, when it gets there we can remove this assumption

section Measurability

lemma measurable_statInfoFun : Measurable statInfoFun.uncurry.uncurry := by
  change Measurable (fun (p : (ℝ × ℝ) × ℝ) ↦ if p.1.2 ≤ p.1.1 then max 0 (p.1.2 - p.1.1 * p.2)
    else max 0 (p.1.1 * p.2 - p.1.2))
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) (by fun_prop)
  · fun_prop
  · fun_prop

lemma stronglyMeasurable_statInfoFun : StronglyMeasurable statInfoFun.uncurry.uncurry := by
  apply Measurable.stronglyMeasurable
  change Measurable (fun (p : (ℝ × ℝ) × ℝ) ↦ if p.1.2 ≤ p.1.1 then max 0 (p.1.2 - p.1.1 * p.2)
    else max 0 (p.1.1 * p.2 - p.1.2))
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) (by fun_prop)
  · fun_prop
  · fun_prop

lemma measurable_statInfoFun2 : Measurable fun γ ↦ statInfoFun β γ x := by
  change Measurable (statInfoFun.uncurry.uncurry ∘ (fun (γ : ℝ) ↦ ((β, γ), x)))
  exact measurable_statInfoFun.comp (by fun_prop)

lemma stronglyMeasurable_statInfoFun3 : StronglyMeasurable (statInfoFun β γ) := by
  change StronglyMeasurable (statInfoFun.uncurry.uncurry ∘ (fun (x : ℝ) ↦ ((β, γ), x)))
  refine measurable_statInfoFun.comp (by fun_prop) |>.stronglyMeasurable

end Measurability

section statInfoFun_x
-- Lemmas useful when we want to consider `statInfoFun` as a function of `x`

lemma statInfoFun_of_le (h : γ ≤ β) : statInfoFun β γ x = max 0 (γ - β * x) := if_pos h

lemma statInfoFun_of_le' (h : γ ≤ β) : statInfoFun β γ = fun x ↦ max 0 (γ - β * x) := by
  ext; exact statInfoFun_of_le h

lemma statInfoFun_of_gt (h : γ > β) : statInfoFun β γ x = max 0 (β * x - γ) := if_neg h.not_le

lemma statInfoFun_of_gt' (h : γ > β) : statInfoFun β γ = fun x ↦ max 0 (β * x - γ) := by
  ext; exact statInfoFun_of_gt h

lemma statInfoFun_of_pos_of_le_of_le (hβ : 0 < β) (hγ : γ ≤ β) (hx : x ≤ γ / β) :
    statInfoFun β γ x = γ - β * x :=
  statInfoFun_of_le hγ ▸ max_eq_right_iff.mpr <| sub_nonneg.mpr <| (le_div_iff₀' hβ).mp hx

lemma statInfoFun_of_pos_of_le_of_ge (hβ : 0 < β) (hγ : γ ≤ β) (hx : x ≥ γ / β) :
    statInfoFun β γ x = 0 :=
  statInfoFun_of_le hγ ▸ max_eq_left_iff.mpr <| sub_nonpos.mpr <| (div_le_iff₀' hβ).mp hx

lemma statInfoFun_of_pos_of_gt_of_le (hβ : 0 < β) (hγ : γ > β) (hx : x ≤ γ / β) :
    statInfoFun β γ x = 0 :=
  statInfoFun_of_gt hγ ▸ max_eq_left_iff.mpr <| sub_nonpos.mpr <| (le_div_iff₀' hβ).mp hx

lemma statInfoFun_of_pos_of_gt_of_ge (hβ : 0 < β) (hγ : γ > β) (hx : x ≥ γ / β) :
    statInfoFun β γ x = β * x - γ :=
  statInfoFun_of_gt hγ ▸ max_eq_right_iff.mpr <| sub_nonneg.mpr <| (div_le_iff₀' hβ).mp hx

lemma statInfoFun_of_neg_of_le_of_le (hβ : β < 0) (hγ : γ ≤ β) (hx : x ≤ γ / β) :
    statInfoFun β γ x = 0 :=
  statInfoFun_of_le hγ ▸  max_eq_left_iff.mpr <| sub_nonpos.mpr <| (le_div_iff_of_neg' hβ).mp hx

lemma statInfoFun_of_neg_of_le_of_ge (hβ : β < 0) (hγ : γ ≤ β) (hx : x ≥ γ / β) :
    statInfoFun β γ x = γ - β * x :=
  statInfoFun_of_le hγ ▸ max_eq_right_iff.mpr <| sub_nonneg.mpr <| (div_le_iff_of_neg' hβ).mp hx

lemma statInfoFun_of_neg_of_gt_of_le (hβ : β < 0) (hγ : γ > β) (hx : x ≤ γ / β) :
    statInfoFun β γ x = β * x - γ :=
  statInfoFun_of_gt hγ ▸ max_eq_right_iff.mpr <| sub_nonneg.mpr <| (le_div_iff_of_neg' hβ).mp hx

lemma statInfoFun_of_neg_of_gt_of_ge (hβ : β < 0) (hγ : γ > β) (hx : x ≥ γ / β) :
    statInfoFun β γ x = 0 :=
  statInfoFun_of_gt hγ ▸ max_eq_left_iff.mpr <| sub_nonpos.mpr <| (div_le_iff_of_neg' hβ).mp hx

lemma statInfoFun_of_one_of_le_one (h : γ ≤ 1) : statInfoFun 1 γ x = max 0 (γ - x) :=
  statInfoFun_one ▸ if_pos h

lemma statInfoFun_of_one_of_one_lt (h : 1 < γ) : statInfoFun 1 γ x = max 0 (x - γ) :=
  statInfoFun_one ▸ if_neg h.not_le

lemma statInfoFun_of_one_of_le_one_of_le (h : γ ≤ 1) (hx : x ≤ γ) : statInfoFun 1 γ x = γ - x :=
  statInfoFun_of_one_of_le_one h ▸ max_eq_right_iff.mpr (sub_nonneg.mpr hx)

lemma statInfoFun_of_one_of_le_one_of_ge (h : γ ≤ 1) (hx : x ≥ γ) : statInfoFun 1 γ x = 0 :=
  statInfoFun_of_one_of_le_one h ▸ max_eq_left_iff.mpr (sub_nonpos.mpr hx)

lemma statInfoFun_of_one_of_one_lt_of_le (h : 1 < γ) (hx : x ≤ γ) : statInfoFun 1 γ x = 0 :=
  statInfoFun_of_one_of_one_lt h ▸ max_eq_left_iff.mpr (sub_nonpos.mpr hx)

lemma statInfoFun_of_one_of_one_lt_of_ge (h : 1 < γ) (hx : x ≥ γ) : statInfoFun 1 γ x = x - γ :=
  statInfoFun_of_one_of_one_lt h ▸ max_eq_right_iff.mpr (sub_nonneg.mpr hx)

@[simp]
lemma statInfoFun_apply_one : statInfoFun β γ 1 = 0 := by
  rcases lt_trichotomy β 0 with hβ | rfl | hβ
  · rcases le_or_lt γ β with hγ | hγ
    · refine statInfoFun_of_neg_of_le_of_le hβ hγ ?_
      rwa [one_le_div_of_neg hβ]
    · refine statInfoFun_of_neg_of_gt_of_ge hβ hγ ?_
      rw [ge_iff_le, div_le_one_of_neg hβ]
      exact hγ.le
  · simp
  · rcases le_or_lt γ β with hγ | hγ
    · refine statInfoFun_of_pos_of_le_of_ge hβ hγ ?_
      rwa [ge_iff_le, div_le_one hβ]
    · refine statInfoFun_of_pos_of_gt_of_le hβ hγ ?_
      rw [one_le_div hβ]
      exact hγ.le

lemma convexOn_statInfoFun (β γ : ℝ) : ConvexOn ℝ univ (statInfoFun β γ) := by
  unfold statInfoFun
  by_cases h : γ ≤ β <;>
  · simp only [h, ↓reduceIte]
    refine (convexOn_const 0 convex_univ).sup ⟨convex_univ, fun x _ y _ a b _ _ hab ↦ le_of_eq ?_⟩
    dsimp
    ring_nf
    simp only [← mul_add, hab, mul_one, show (-(a * γ) - b * γ) = -(a + b) * γ from by ring,
      add_assoc, sub_eq_add_neg, neg_mul, one_mul]

lemma continuousAt_statInfoFun (hx : x ≠ γ / β) :
    ContinuousAt (statInfoFun β γ) x := by
  rcases le_or_lt γ β with hγ | hγ
  · rw [statInfoFun_of_le' hγ]
    sorry
  · rw [statInfoFun_of_gt' hγ]
    sorry

lemma continuousAt_statInfoFun_zero (hγ : γ ≠ 0) :
    ContinuousAt (statInfoFun β γ) 0 := by
  by_cases hβ : β = 0
  · simp only [hβ, statInfoFun_zero']
    fun_prop
  refine continuousAt_statInfoFun ?_
  symm
  rw [ne_eq, div_eq_zero_iff]
  simp [hβ, hγ]

lemma continuousWithinAt_statInfoFun_zero :
    ContinuousWithinAt (statInfoFun β γ) (Ioi 0) 0 := by
  by_cases hγ : γ = 0
  · rcases lt_trichotomy β 0 with hβ | rfl | hβ
    · simp only [hγ, statInfoFun_of_gt' hβ, sub_zero]
      have : (fun x ↦ max 0 (β * x)) =ᶠ[𝓝[>] 0] fun _ ↦ 0 := by
        suffices ∀ᶠ x in 𝓝[>] 0, β * x ≤ 0 by
          filter_upwards [this] with x hx
          rw [max_eq_left hx]
        exact eventually_nhdsWithin_of_forall
          fun x hx ↦ (mul_nonpos_of_nonpos_of_nonneg hβ.le hx.le)
      refine ContinuousWithinAt.congr_of_eventuallyEq ?_ this (by simp)
      refine Continuous.continuousWithinAt ?_
      fun_prop
    · simp only [statInfoFun_zero']
      refine ContinuousAt.continuousWithinAt ?_
      fun_prop
    · simp only [hγ, statInfoFun_of_le' hβ.le, zero_sub]
      have : (fun x ↦ max 0 (-(β * x))) =ᶠ[𝓝[>] 0] fun _ ↦ 0 := by
        suffices ∀ᶠ x in 𝓝[>] 0, -(β * x) ≤ 0 by
          filter_upwards [this] with x hx
          rw [max_eq_left hx]
        simp only [Left.neg_nonpos_iff]
        exact eventually_nhdsWithin_of_forall fun x hx ↦ (mul_nonneg hβ.le hx.le)
      refine ContinuousWithinAt.congr_of_eventuallyEq ?_ this (by simp)
      refine Continuous.continuousWithinAt ?_
      fun_prop
  · exact ContinuousAt.continuousWithinAt (continuousAt_statInfoFun_zero hγ)

section rightDeriv

lemma rightDeriv_statInfoFun_of_pos_of_le_of_lt (hβ : 0 < β) (hγ : γ ≤ β) (hx : x < γ / β) :
    rightDeriv (statInfoFun β γ) x = - β := by
  rw [statInfoFun_of_le' hγ]
  sorry

lemma rightDeriv_statInfoFun_of_pos_of_le_of_ge (hβ : 0 < β) (hγ : γ ≤ β) (hx : x ≥ γ / β) :
    rightDeriv (statInfoFun β γ) x = 0 :=
  sorry

lemma rightDeriv_one_statInfoFun_of_pos_of_le_ (hβ : 0 < β) (hγ : γ ≤ β) :
    rightDeriv (statInfoFun β γ) 1 = 0 := by
  refine rightDeriv_statInfoFun_of_pos_of_le_of_ge hβ hγ ?_
  rwa [ge_iff_le, div_le_one hβ]

lemma rightDeriv_statInfoFun_of_pos_of_gt_of_lt (hβ : 0 < β) (hγ : γ > β) (hx : x < γ / β) :
    rightDeriv (statInfoFun β γ) x = 0 :=
  sorry

lemma rightDeriv_statInfoFun_of_pos_of_gt_of_ge (hβ : 0 < β) (hγ : γ > β) (hx : x ≥ γ / β) :
    rightDeriv (statInfoFun β γ) x = β :=
  sorry

lemma rightDeriv_one_statInfoFun_of_pos_of_gt (hβ : 0 < β) (hγ : γ > β) :
    rightDeriv (statInfoFun β γ) 1 = 0 := by
  refine rightDeriv_statInfoFun_of_pos_of_gt_of_lt hβ hγ ?_
  rwa [one_lt_div hβ]

lemma rightDeriv_statInfoFun_of_neg_of_le_of_lt (hβ : β < 0) (hγ : γ ≤ β) (hx : x < γ / β) :
    rightDeriv (statInfoFun β γ) x = 0 :=
  sorry

lemma rightDeriv_statInfoFun_of_neg_of_le_of_ge (hβ : β < 0) (hγ : γ ≤ β) (hx : x ≥ γ / β) :
    rightDeriv (statInfoFun β γ) x = - β :=
  sorry

lemma rightDeriv_one_statInfoFun_of_neg_of_eq (hβ : β < 0) :
    rightDeriv (statInfoFun β β) 1 = - β := by
  refine rightDeriv_statInfoFun_of_neg_of_le_of_ge hβ le_rfl ?_
  simp [hβ.ne]

lemma rightDeriv_one_statInfoFun_of_neg_of_lt (hβ : β < 0) (hγ : γ < β) :
    rightDeriv (statInfoFun β γ) 1 = 0 := by
  refine rightDeriv_statInfoFun_of_neg_of_le_of_lt hβ hγ.le ?_
  rwa [one_lt_div_of_neg hβ]

lemma rightDeriv_statInfoFun_of_neg_of_gt_of_lt (hβ : β < 0) (hγ : γ > β) (hx : x < γ / β) :
    rightDeriv (statInfoFun β γ) x = β :=
  sorry

lemma rightDeriv_statInfoFun_of_neg_of_gt_of_ge (hβ : β < 0) (hγ : γ > β) (hx : x ≥ γ / β) :
    rightDeriv (statInfoFun β γ) x = 0 :=
  sorry

lemma rightDeriv_one_statInfoFun_of_neg_of_gt (hβ : β < 0) (hγ : γ > β) :
    rightDeriv (statInfoFun β γ) 1 = 0 := by
  refine rightDeriv_statInfoFun_of_neg_of_gt_of_ge hβ hγ ?_
  rw [ge_iff_le, div_le_one_of_neg hβ]
  exact hγ.le

lemma rightDeriv_statInfoFun_one_of_le_one_of_le (h : γ ≤ 1) (hx : x < γ) :
    rightDeriv (statInfoFun 1 γ) x = -1 :=
  sorry

lemma rightDeriv_statInfoFun_one_of_le_one_of_ge (h : γ ≤ 1) (hx : x ≥ γ) :
    rightDeriv (statInfoFun 1 γ) x = 0 :=
  sorry

lemma rightDeriv_statInfoFun_one_of_one_lt_of_lt (h : 1 < γ) (hx : x < γ) :
    rightDeriv (statInfoFun 1 γ) x = 0 :=
  sorry

lemma rightDeriv_statInfoFun_one_of_one_lt_of_ge (h : 1 < γ) (hx : x ≥ γ) :
    rightDeriv (statInfoFun 1 γ) x = 1 :=
  sorry

lemma rightDeriv_one_statInfoFun_one :
    rightDeriv (statInfoFun 1 γ) 1 = 0 := by
  rcases le_or_lt γ 1 with h | h
  · exact rightDeriv_statInfoFun_one_of_le_one_of_ge h h
  · exact rightDeriv_statInfoFun_one_of_one_lt_of_lt h h

end rightDeriv

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
  · simp [statInfoFun, hγβ, indicator, hγβ.trans (le_mul_of_one_le_right hβ hx), hγβ.not_lt]
  · by_cases hγβx : γ ≤ β * x
    · simp [statInfoFun, hγβ, hγβx, lt_of_not_ge hγβ]
    · simp [statInfoFun, hγβ, hγβx, le_of_not_ge hγβx]

lemma statInfoFun_of_nonpos_of_right_le_one (hβ : β ≤ 0) (hx : x ≤ 1) :
    statInfoFun β γ x = (Ioc β (β * x)).indicator (fun y ↦ β * x - y) γ := by
  by_cases hγβ : γ ≤ β
  · simp only [statInfoFun, hγβ, ↓reduceIte, indicator, mem_Ioc, hγβ.not_lt, false_and,
      max_eq_left_iff, tsub_le_iff_right, zero_add]
    suffices -β * x ≤ -γ from by simpa only [neg_mul, neg_le_neg_iff]
    exact (mul_le_of_le_one_right (neg_nonneg.mpr hβ) hx).trans (neg_le_neg_iff.mpr hγβ)
  · by_cases hγβx : γ ≤ β * x
    · simp [statInfoFun, hγβx, lt_of_not_ge hγβ]
    · simp [statInfoFun, hγβ, hγβx, le_of_not_ge hγβx]

lemma statInfoFun_of_nonpos_of_one_le_right (hβ : β ≤ 0) (hx : 1 ≤ x) :
    statInfoFun β γ x = (Ioc (β * x) β).indicator (fun y ↦ y - β * x) γ := by
  by_cases hγβ : γ ≤ β
  · by_cases hβxγ : β * x < γ
    · simp [statInfoFun, indicator, hβxγ, hβxγ.le]
    · simp [statInfoFun, hγβ, hβxγ, (le_of_not_gt hβxγ)]
  · simp only [statInfoFun, hγβ, ↓reduceIte, mem_Ioc, and_false, not_false_eq_true,
      indicator_of_not_mem, max_eq_left_iff, tsub_le_iff_right, zero_add]
    suffices -β * x ≥ -γ from by simpa only [neg_mul, neg_le_neg_iff]
    exact ((neg_lt_neg_iff.mpr (lt_of_not_ge hγβ)).trans_le
      ((le_mul_of_one_le_right (neg_nonneg.mpr hβ) hx))).le

lemma statInfoFun_of_one_of_one_le_right (h : 1 ≤ x) :
    statInfoFun 1 γ x = (Ioc 1 x).indicator (fun y ↦ x - y) γ := by
  convert statInfoFun_of_nonneg_of_one_le_right _ h <;> simp

lemma statInfoFun_of_one_of_right_le_one (h : x ≤ 1) :
    statInfoFun 1 γ x = (Ioc x 1).indicator (fun y ↦ y - x) γ := by
  convert statInfoFun_of_nonneg_of_right_le_one _ h <;> simp

lemma statInfoFun_one_zero_right : statInfoFun 1 γ 0 = (Ioc 0 1).indicator id γ := by
  rw [statInfoFun_of_one_of_right_le_one zero_le_one]
  simp only [sub_zero]
  rfl

lemma statInfoFun_le_of_nonneg_of_right_le_one (hβ : 0 ≤ β) (hx : x ≤ 1) :
    statInfoFun β γ x ≤ (Ioc (β * x) β).indicator (fun _ ↦ β - β * x) γ := by
  rw [statInfoFun_of_nonneg_of_right_le_one hβ hx]
  refine indicator_rel_indicator le_rfl fun ⟨_, hγ⟩ ↦ ?_
  simp [hγ]

lemma statInfoFun_le_of_nonneg_of_one_le_right (hβ : 0 ≤ β) (hx : 1 ≤ x) :
    statInfoFun β γ x ≤ (Ioc β (β * x)).indicator (fun _ ↦ β * x - β) γ := by
  rw [statInfoFun_of_nonneg_of_one_le_right hβ hx]
  refine indicator_rel_indicator le_rfl fun ⟨hβγ, _⟩ ↦ ?_
  simp only [sub_eq_add_neg, add_le_add_iff_left, neg_le_neg_iff, hβγ.le]

lemma statInfoFun_le_of_nonpos_of_right_le_one (hβ : β ≤ 0) (hx : x ≤ 1) :
    statInfoFun β γ x ≤ (Ioc β (β * x)).indicator (fun _ ↦ β * x - β) γ := by
  rw [statInfoFun_of_nonpos_of_right_le_one hβ hx]
  refine indicator_rel_indicator le_rfl fun ⟨hγβ, _⟩ ↦ ?_
  simp only [sub_eq_add_neg, add_le_add_iff_left, neg_le_neg_iff, hγβ.le]

lemma statInfoFun_le_of_nonpos_of_one_le_right (hβ : β ≤ 0) (hx : 1 ≤ x) :
    statInfoFun β γ x ≤ (Ioc (β * x) β).indicator (fun _ ↦ β - β * x) γ := by
  rw [statInfoFun_of_nonpos_of_one_le_right hβ hx]
  refine indicator_rel_indicator le_rfl fun ⟨_, hγ⟩ ↦ ?_
  simp [hγ]

lemma lintegral_nnnorm_statInfoFun_le {μ : Measure ℝ} (β x : ℝ) :
    ∫⁻ γ, ↑‖statInfoFun β γ x‖₊ ∂μ ≤ (μ (uIoc (β * x) β)) * (ENNReal.ofReal |β - β * x|) := by
  simp_rw [Real.nnnorm_of_nonneg (statInfoFun_nonneg _ _ _),
    ← ENNReal.ofReal_eq_coe_nnreal (statInfoFun_nonneg _ _ _)]
  rcases le_total β 0 with (hβ | hβ) <;> rcases le_total x 1 with (hx | hx)
  · have hββx : β ≤ β * x := by exact le_mul_of_le_one_right hβ hx
    calc
      _ ≤ ∫⁻ γ, ENNReal.ofReal ((Ioc β (β * x)).indicator (fun _ ↦ β * x - β) γ) ∂μ :=
        lintegral_mono fun _ ↦ ENNReal.ofReal_le_ofReal <|
          statInfoFun_le_of_nonpos_of_right_le_one hβ hx
      _ = ∫⁻ γ,  ((Ioc β (β * x)).indicator (fun _ ↦ ENNReal.ofReal (β * x - β)) γ) ∂μ := by
        simp [Set.comp_indicator]
      _ ≤ ENNReal.ofReal (β * x - β) * μ (Ioc β (β * x)) := lintegral_indicator_const_le _ _
      _ = μ (Ι (β * x) β) * ENNReal.ofReal |β - β * x| := by
        rw [uIoc_of_ge hββx, mul_comm, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hββx)]
  · have hβxβ : β * x ≤ β := by exact mul_le_of_one_le_right hβ hx
    calc
      _ ≤ ∫⁻ γ, ENNReal.ofReal ((Ioc (β * x) β).indicator (fun _ ↦ β - β * x) γ) ∂μ :=
        lintegral_mono fun _ ↦ ENNReal.ofReal_le_ofReal <|
          statInfoFun_le_of_nonpos_of_one_le_right hβ hx
      _ = ∫⁻ γ,  ((Ioc (β * x) β).indicator (fun _ ↦ ENNReal.ofReal (β - β * x)) γ) ∂μ := by
        simp [Set.comp_indicator]
      _ ≤ ENNReal.ofReal (β - β * x) * μ (Ioc (β * x) β) := lintegral_indicator_const_le _ _
      _ = μ (Ι (β * x) β) * ENNReal.ofReal |β - β * x| := by
        rw [uIoc_comm, uIoc_of_ge hβxβ, abs_of_nonneg (sub_nonneg.mpr hβxβ), mul_comm]
  · have hββx : β * x ≤ β := by exact mul_le_of_le_one_right hβ hx
    calc
      _ ≤ ∫⁻ γ, ENNReal.ofReal ((Ioc (β * x) β).indicator (fun _ ↦ β - β * x) γ) ∂μ :=
        lintegral_mono fun _ ↦ ENNReal.ofReal_le_ofReal <|
          statInfoFun_le_of_nonneg_of_right_le_one hβ hx
      _ = ∫⁻ γ,  ((Ioc (β * x) β).indicator (fun _ ↦ ENNReal.ofReal (β - β * x)) γ) ∂μ := by
        simp [Set.comp_indicator]
      _ ≤ ENNReal.ofReal (β - β * x) * μ (Ioc (β * x) β) := lintegral_indicator_const_le _ _
      _ = μ (Ι (β * x) β) * ENNReal.ofReal |β - β * x| := by
        rw [uIoc_comm, uIoc_of_ge hββx, abs_of_nonneg (sub_nonneg.mpr hββx), mul_comm]
  · have hβxβ : β ≤ β * x := by exact le_mul_of_one_le_right hβ hx
    calc
      _ ≤ ∫⁻ γ, ENNReal.ofReal ((Ioc β (β * x)).indicator (fun _ ↦ β * x - β) γ) ∂μ :=
        lintegral_mono fun _ ↦ ENNReal.ofReal_le_ofReal <|
          statInfoFun_le_of_nonneg_of_one_le_right hβ hx
      _ = ∫⁻ γ,  ((Ioc β (β * x)).indicator (fun _ ↦ ENNReal.ofReal (β * x - β)) γ) ∂μ := by
        simp [Set.comp_indicator]
      _ ≤ ENNReal.ofReal (β * x - β) * μ (Ioc β (β * x)) := lintegral_indicator_const_le _ _
      _ = μ (Ι (β * x) β) * ENNReal.ofReal |β - β * x| := by
        rw [uIoc_of_ge hβxβ, mul_comm, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hβxβ)]

lemma integrable_statInfoFun {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] (β x : ℝ) :
    Integrable (fun γ ↦ statInfoFun β γ x) μ := by
  refine ⟨measurable_statInfoFun2.stronglyMeasurable.aestronglyMeasurable, ?_⟩
  refine ((lintegral_nnnorm_statInfoFun_le _ _).trans_lt ?_)
  refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
  exact (measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top

lemma integrable_statInfoFun_one_iff_of_ge {μ : Measure ℝ} {x : ℝ} (hx : 1 ≤ x) :
    Integrable (fun γ ↦ statInfoFun 1 γ x) μ ↔ IntegrableOn (fun y ↦ x - y) (Ioc 1 x) μ := by
  simp_rw [statInfoFun_of_one_of_one_le_right hx]
  rw [integrable_indicator_iff]
  exact measurableSet_Ioc

lemma integrable_statInfoFun_one_iff_of_le {μ : Measure ℝ} {x : ℝ} (hx : x ≤ 1) :
    Integrable (fun γ ↦ statInfoFun 1 γ x) μ ↔ IntegrableOn (fun y ↦ y - x) (Ioc x 1) μ := by
  simp_rw [statInfoFun_of_one_of_right_le_one hx]
  rw [integrable_indicator_iff]
  exact measurableSet_Ioc

lemma integrable_statInfoFun_one_iff {μ : Measure ℝ} (x : ℝ) :
    Integrable (fun γ ↦ statInfoFun 1 γ x) μ ↔ IntegrableOn (fun y ↦ y - x) (uIoc 1 x) μ := by
  rcases le_total 1 x with hx | hx
  · simp only [hx, uIoc_of_le]
    have : (-fun y ↦ x - y) = (fun y ↦ y - x) := by ext; simp
    rw [integrable_statInfoFun_one_iff_of_ge hx, IntegrableOn, IntegrableOn, ← this,
      integrable_neg_iff]
  · rw [integrable_statInfoFun_one_iff_of_le hx]
    simp [hx]

lemma integrable_statInfoFun_one_iff' {μ : Measure ℝ} (x : ℝ) :
    Integrable (fun γ ↦ statInfoFun 1 γ x) μ ↔ IntegrableOn (fun y ↦ x - y) (uIoc 1 x) μ := by
  have : (-fun y ↦ x - y) = (fun y ↦ y - x) := by ext; simp
  rw [integrable_statInfoFun_one_iff, IntegrableOn, IntegrableOn, ← this,
      integrable_neg_iff]

end statInfoFun_γ

end ProbabilityTheory

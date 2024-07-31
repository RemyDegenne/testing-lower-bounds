/-
Copyright (c) 2024 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import TestingLowerBounds.DerivAtTop
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.MeasureTheory.Measure.Regular

open MeasureTheory Set Filter Topology StieltjesFunction

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳} {f : ℝ → ℝ} {β γ x t : ℝ}

-- To play with this function go to https://www.geogebra.org/calculator/jaymzqtm, there the notation is: b for β, c for γ, X for x. h is statInfoFun seen as a function of x, f is statInfoFun seen as a function of γ.
/-- The hockey-stick function, it is related to the statistical information divergence. -/
noncomputable
def statInfoFun (β γ x : ℝ) : ℝ := if γ ≤ β then max 0 (γ - β * x) else max 0 (β * x - γ)

lemma statInfoFun_nonneg (β γ x : ℝ) : 0 ≤ statInfoFun β γ x := by
  simp_rw [statInfoFun]
  split_ifs <;> simp

@[simp]
lemma statInfoFun_of_one : statInfoFun 1 γ x = if γ ≤ 1 then max 0 (γ - x) else max 0 (x - γ) := by
  simp_rw [statInfoFun, one_mul]

@[simp]
lemma statInfoFun_of_zero : statInfoFun 0 γ x = 0 := by simp_all [statInfoFun, le_of_lt]

lemma const_mul_statInfoFun {a : ℝ} (ha : 0 ≤ a) :
    a * statInfoFun β γ x = statInfoFun (a * β) (a * γ) x := by
  simp_rw [statInfoFun, mul_ite, mul_max_of_nonneg _ _ ha, mul_sub, mul_zero, mul_assoc]
  rcases lt_or_eq_of_le ha with (ha | rfl)
  · simp_rw [mul_le_mul_left ha]
  · simp

--TODO: for now I will leave the continuity assumption in some lemmas, it should be derived from the convexity but the lemma is not yet in mathlib, when it gets there we can remove this assumption

section Measurability

lemma stronglymeasurable_statInfoFun : StronglyMeasurable statInfoFun.uncurry.uncurry := by
  apply Measurable.stronglyMeasurable
  change Measurable (fun (p : (ℝ × ℝ) × ℝ) ↦ if p.1.2 ≤ p.1.1 then max 0 (p.1.2 - p.1.1 * p.2)
    else max 0 (p.1.1 * p.2 - p.1.2))
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) (by fun_prop)
  · fun_prop
  · fun_prop

lemma measurable_statInfoFun2 : Measurable fun γ ↦ statInfoFun β γ x := by
  change Measurable (statInfoFun.uncurry.uncurry ∘ (fun (γ : ℝ) ↦ ((β, γ), x)))
  exact stronglymeasurable_statInfoFun.measurable.comp (by fun_prop)

lemma stronglyMeasurable_statInfoFun3 : StronglyMeasurable (statInfoFun β γ) := by
  change StronglyMeasurable (statInfoFun.uncurry.uncurry ∘ (fun (x : ℝ) ↦ ((β, γ), x)))
  refine stronglymeasurable_statInfoFun.measurable.comp (by fun_prop) |>.stronglyMeasurable

end Measurability

section statInfoFun_x
-- Lemmas useful when we want to consider `statInfoFun` as a function of `x`

lemma statInfoFun_of_le (h : γ ≤ β) : statInfoFun β γ x = max 0 (γ - β * x) := if_pos h

lemma statInfoFun_of_gt (h : γ > β) : statInfoFun β γ x = max 0 (β * x - γ) := if_neg h.not_le

lemma statInfoFun_of_pos_of_le_of_le (hβ : 0 < β) (hγ : γ ≤ β) (hx : x ≤ γ / β) :
    statInfoFun β γ x = γ - β * x :=
  statInfoFun_of_le hγ ▸ max_eq_right_iff.mpr <| sub_nonneg.mpr <| (le_div_iff' hβ).mp hx

lemma statInfoFun_of_pos_of_le_of_ge (hβ : 0 < β) (hγ : γ ≤ β) (hx : x ≥ γ / β) :
    statInfoFun β γ x = 0 :=
  statInfoFun_of_le hγ ▸ max_eq_left_iff.mpr <| sub_nonpos.mpr <| (div_le_iff' hβ).mp hx

lemma statInfoFun_of_pos_of_gt_of_le (hβ : 0 < β) (hγ : γ > β) (hx : x ≤ γ / β) :
    statInfoFun β γ x = 0 :=
  statInfoFun_of_gt hγ ▸ max_eq_left_iff.mpr <| sub_nonpos.mpr <| (le_div_iff' hβ).mp hx

lemma statInfoFun_of_pos_of_gt_of_ge (hβ : 0 < β) (hγ : γ > β) (hx : x ≥ γ / β) :
    statInfoFun β γ x = β * x - γ :=
  statInfoFun_of_gt hγ ▸ max_eq_right_iff.mpr <| sub_nonneg.mpr <| (div_le_iff' hβ).mp hx

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
  statInfoFun_of_one ▸ if_pos h

lemma statInfoFun_of_one_of_one_lt (h : 1 < γ) : statInfoFun 1 γ x = max 0 (x - γ) :=
  statInfoFun_of_one ▸ if_neg h.not_le

lemma statInfoFun_of_one_of_le_one_of_le (h : γ ≤ 1) (hx : x ≤ γ) : statInfoFun 1 γ x = γ - x :=
  statInfoFun_of_one_of_le_one h ▸ max_eq_right_iff.mpr (sub_nonneg.mpr hx)

lemma statInfoFun_of_one_of_le_one_of_ge (h : γ ≤ 1) (hx : x ≥ γ) : statInfoFun 1 γ x = 0 :=
  statInfoFun_of_one_of_le_one h ▸ max_eq_left_iff.mpr (sub_nonpos.mpr hx)

lemma statInfoFun_of_one_of_one_lt_of_le (h : 1 < γ) (hx : x ≤ γ) : statInfoFun 1 γ x = 0 :=
  statInfoFun_of_one_of_one_lt h ▸ max_eq_left_iff.mpr (sub_nonpos.mpr hx)

lemma statInfoFun_of_one_of_one_lt_of_ge (h : 1 < γ) (hx : x ≥ γ) : statInfoFun 1 γ x = x - γ :=
  statInfoFun_of_one_of_one_lt h ▸ max_eq_right_iff.mpr (sub_nonneg.mpr hx)

lemma convexOn_statInfoFun (β γ : ℝ) : ConvexOn ℝ univ (fun x ↦ statInfoFun β γ x) := by
  unfold statInfoFun
  by_cases h : γ ≤ β <;>
  · simp only [h, ↓reduceIte]
    refine (convexOn_const 0 convex_univ).sup ⟨convex_univ, fun x _ y _ a b _ _ hab ↦ le_of_eq ?_⟩
    dsimp
    ring_nf
    simp only [← mul_add, hab, mul_one, show (-(a * γ) - b * γ) = -(a + b) * γ from by ring,
      add_assoc, sub_eq_add_neg, neg_mul, one_mul]

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
    swap; exact (ConvexOn.ConvexOn.const_mul _).subset (subset_univ _) (convex_Ici _)
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

lemma derivAtTop_statInfoFun_ne_top (β γ : ℝ) : derivAtTop (fun x ↦ statInfoFun β γ x) ≠ ⊤ := by
  rcases le_total 0 β with (hβ | hβ) <;> rcases le_or_lt γ β with (hγ | hγ) <;>
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
  refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_ne_top
  exact (measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top |>.ne

end statInfoFun_γ

end ProbabilityTheory

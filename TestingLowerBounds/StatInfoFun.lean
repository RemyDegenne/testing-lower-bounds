/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.ForMathlib.ByParts
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import TestingLowerBounds.ForMathlib.Stieltjes
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Tactic.FunProp.Measurable
import Mathlib.MeasureTheory.Constructions.Prod.Integral

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

lemma measurable_statInfoFun3 : Measurable fun x ↦ statInfoFun β γ x := by
  change Measurable (statInfoFun.uncurry.uncurry ∘ (fun (x : ℝ) ↦ ((β, γ), x)))
  exact stronglymeasurable_statInfoFun.measurable.comp (by fun_prop)

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

lemma tendsto_statInfoFun_div_at_top_of_pos_of_le (hβ : 0 < β) (hγ : γ ≤ β) :
    Tendsto (fun x ↦ statInfoFun β γ x / x) atTop (𝓝 0) := by
  refine tendsto_atTop_of_eventually_const (fun x hx ↦ ?_) (i₀ := γ / β)
  rw [statInfoFun_of_le hγ, div_eq_zero_iff]
  exact Or.inl <| max_eq_left_iff.mpr <| tsub_nonpos.mpr <| (div_le_iff' hβ).mp hx

lemma tendsto_statInfoFun_div_at_top_of_pos_of_gt (hβ : 0 < β) (hγ : γ > β) :
    Tendsto (fun x ↦ statInfoFun β γ x / x) atTop (𝓝 β) := by
  have h : (fun x ↦ β + -γ / x) =ᶠ[atTop] fun x ↦ statInfoFun β γ x / x := by
    filter_upwards [eventually_ge_atTop (γ / β), eventually_ne_atTop 0] with x hx hx'
    rw [statInfoFun_of_pos_of_gt_of_ge hβ hγ hx]
    ring_nf
    simp_rw [mul_assoc, mul_inv_cancel hx', mul_one]
  nth_rw 2 [← add_zero β]
  refine Tendsto.congr' h (Tendsto.const_add β ?_)
  exact Tendsto.div_atTop tendsto_const_nhds fun _ a ↦ a

lemma tendsto_statInfoFun_div_at_top_of_neg_of_le (hβ : β < 0) (hγ : γ ≤ β) :
    Tendsto (fun x ↦ statInfoFun β γ x / x) atTop (𝓝 (-β)) := by
  have h : (fun x ↦ γ / x - β) =ᶠ[atTop] fun x ↦ statInfoFun β γ x / x := by
    filter_upwards [eventually_ge_atTop (γ / β), eventually_ne_atTop 0] with x hx hx'
    rw [statInfoFun_of_neg_of_le_of_ge hβ hγ hx]
    ring_nf
    simp_rw [mul_inv_cancel hx', one_mul]
  rw [neg_eq_zero_sub β]
  refine Tendsto.congr' h (Tendsto.sub_const ?_ β)
  exact Tendsto.div_atTop tendsto_const_nhds fun _ a ↦ a

lemma tendsto_statInfoFun_div_at_top_of_neg_of_gt (hβ : β < 0) (hγ : γ > β) :
    Tendsto (fun x ↦ statInfoFun β γ x / x) atTop (𝓝 0) := by
  refine tendsto_atTop_of_eventually_const (fun x hx ↦ ?_) (i₀ := γ / β)
  rw [statInfoFun_of_gt hγ, div_eq_zero_iff]
  refine Or.inl <| max_eq_left_iff.mpr <| tsub_nonpos.mpr <| (div_le_iff_of_neg' hβ).mp hx

lemma derivAtTop_statInfoFun_of_nonneg_of_le (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    derivAtTop (fun x ↦ statInfoFun β γ x) = 0 := by
  rcases eq_or_lt_of_le hβ with (rfl | hβ)
  · simp
  exact derivAtTop_of_tendsto (tendsto_statInfoFun_div_at_top_of_pos_of_le hβ hγ)

lemma derivAtTop_statInfoFun_of_nonneg_of_gt (hβ : 0 ≤ β) (hγ : γ > β) :
    derivAtTop (fun x ↦ statInfoFun β γ x) = β := by
  rcases eq_or_lt_of_le hβ with (rfl | hβ)
  · simp
  exact derivAtTop_of_tendsto (tendsto_statInfoFun_div_at_top_of_pos_of_gt hβ hγ)

lemma derivAtTop_statInfoFun_of_nonpos_of_le (hβ : β ≤ 0) (hγ : γ ≤ β) :
    derivAtTop (fun x ↦ statInfoFun β γ x) = -β := by
  rcases eq_or_lt_of_le hβ with (rfl | hβ)
  · simp
  exact derivAtTop_of_tendsto (tendsto_statInfoFun_div_at_top_of_neg_of_le hβ hγ)

lemma derivAtTop_statInfoFun_of_nonpos_of_gt (hβ : β ≤ 0) (hγ : γ > β) :
    derivAtTop (fun x ↦ statInfoFun β γ x) = 0 := by
  rcases eq_or_lt_of_le hβ with (rfl | hβ)
  · simp
  exact derivAtTop_of_tendsto (tendsto_statInfoFun_div_at_top_of_neg_of_gt hβ hγ)

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

--PRed to mathlib, see #14199, when it gets merged and we bump remove these 2 lemmas
@[simp] lemma uIoc_of_ge {α : Type u_1} [LinearOrder α] {a b : α} (h : b ≤ a) :
  Ι a b = Ioc b a := by simp [uIoc, h]
lemma uIoc_subset_uIcc {α : Type u_1} [LinearOrder α] {a b : α} :
    Ι a b ⊆ uIcc a b := Ioc_subset_Icc_self

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

section fDiv

lemma nnReal_mul_fDiv {a : NNReal} :
    a * fDiv (fun x ↦ statInfoFun β γ x) μ ν = fDiv (statInfoFun (a * β) (a * γ)) μ ν := by
  change (a.1 : EReal) * _ = _
  rw [← fDiv_mul a.2 ((convexOn_statInfoFun β γ).subset (fun _ _ ↦ trivial) (convex_Ici 0)) μ ν]
  simp_rw [const_mul_statInfoFun a.2]
  rfl

end fDiv

section CurvatureMeasure

--should we define this to be some junk value if f is not convex? this way we could avoid having to state the convexity every time
-- this may be put in some other place, maybe directly in the stieltjes file
/-- The curvature measure induced by a convex function. It is defined as the only measure that has
the right derivative of the function as a CDF. -/
noncomputable
def curvatureMeasure (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) : Measure ℝ :=
  (StieltjesFunction.rightDeriv_of_convex f hf).measure

instance (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) : IsLocallyFiniteMeasure (curvatureMeasure f hf) := by
  unfold curvatureMeasure
  infer_instance

lemma generalized_taylor (hf : ConvexOn ℝ univ f) (hf_cont : Continuous f) {a b : ℝ} :
    f b - f a - (rightDeriv f a) * (b - a)  = ∫ x in a..b, b - x ∂(curvatureMeasure f hf) := by
  have h_int : IntervalIntegrable (rightDeriv f) ℙ a b := hf.rightDeriv_mono.intervalIntegrable
  rw [← intervalIntegral.integral_eq_sub_of_hasDeriv_right hf_cont.continuousOn
    (fun x _ ↦ hf.hadDerivWithinAt_rightDeriv_of_convexOn x) h_int]
  simp_rw [← neg_sub _ b, intervalIntegral.integral_neg, curvatureMeasure,
    mul_neg, sub_neg_eq_add, mul_comm _ (a - b)]
  let g := StieltjesFunction.id + StieltjesFunction.const (-b)
  have hg : g = fun x ↦ x - b := rfl
  rw [← hg, integral_stieltjes_meas_by_parts g (rightDeriv_of_convex f hf)]
  simp only [Real.volume_eq_stieltjes_id, add_apply, id_apply, id_eq, const_apply, add_right_neg,
    zero_mul, zero_sub, measure_add, measure_const, add_zero, neg_sub, sub_neg_eq_add, g]
  rfl

lemma fun_eq_integral_statInfoFun_curvatureMeasure (hf_cvx : ConvexOn ℝ univ f)
    (hf_cont : Continuous f) (hf_one : f 1 = 0) (hfderiv_one : rightDeriv f 1 = 0) :
    f t = ∫ y, statInfoFun 1 y t ∂(curvatureMeasure f hf_cvx) := by
  have h :
      f t - f 1 - (rightDeriv f 1) * (t - 1) = ∫ x in (1)..t, t - x ∂(curvatureMeasure f hf_cvx) :=
    generalized_taylor hf_cvx hf_cont
  rw [hf_one, hfderiv_one, sub_zero, zero_mul, sub_zero] at h
  rw [h]
  rcases le_total t 1 with (ht | ht)
  · simp_rw [statInfoFun_of_one_of_right_le_one ht, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_ge ht, ← integral_neg, neg_sub]
  · simp_rw [statInfoFun_of_one_of_one_le_right ht, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_le ht]

-- TODO: think about the case when the function is not integrable (`h_int`), can we prove that in this case the rhs is also not integrable?

lemma fDiv_eq_integral_fDiv_statInfoFun_curvatureMeasure_of_absolutelyContinuous
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (hf_one : f 1 = 0)
    (hfderiv_one : rightDeriv f 1 = 0) (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ac : μ ≪ ν) :
    fDiv f μ ν = ∫ x, (fDiv (statInfoFun 1 x) μ ν).toReal ∂(curvatureMeasure f hf_cvx) := by
  have h_int' (γ : ℝ) : Integrable (fun x ↦ statInfoFun 1 γ ((∂μ/∂ν) x).toReal) ν := by
    refine integrable_f_rnDeriv_of_derivAtTop_ne_top _ _
      measurable_statInfoFun3.stronglyMeasurable ?_ ?_
    · exact (convexOn_statInfoFun 1 γ).subset (fun _ _ ↦ trivial) (convex_Ici 0)
    · by_cases h : γ ≤ 1
      · exact derivAtTop_statInfoFun_of_nonneg_of_le (zero_le_one) h ▸ EReal.zero_ne_top
      · exact derivAtTop_statInfoFun_of_nonneg_of_gt (zero_le_one) (lt_of_not_ge h) ▸
          EReal.coe_ne_top 1
  classical
  rw [fDiv_of_absolutelyContinuous h_ac, if_pos h_int, EReal.coe_eq_coe_iff]
  simp_rw [fDiv_of_absolutelyContinuous h_ac, if_pos (h_int' _), EReal.toReal_coe,
    fun_eq_integral_statInfoFun_curvatureMeasure hf_cvx hf_cont hf_one hfderiv_one]
  have h_meas : Measurable (fun x γ ↦ statInfoFun 1 γ ((∂μ/∂ν) x).toReal).uncurry := by
    change Measurable
      (statInfoFun.uncurry.uncurry ∘ (fun (xγ : 𝒳 × ℝ) ↦ ((1, xγ.2), ((∂μ/∂ν) xγ.1).toReal)))
    refine stronglymeasurable_statInfoFun.measurable.comp ?_
    refine (measurable_const.prod_mk measurable_snd).prod_mk ?_
    exact ((Measure.measurable_rnDeriv μ ν).comp measurable_fst).ennreal_toReal
  have int_eq_lint : ∫ x, ∫ γ, statInfoFun 1 γ ((∂μ/∂ν) x).toReal ∂curvatureMeasure f hf_cvx ∂ν
      = (∫⁻ x, ∫⁻ γ, ENNReal.ofReal (statInfoFun 1 γ ((∂μ/∂ν) x).toReal)
        ∂curvatureMeasure f hf_cvx ∂ν).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    rotate_left
    · exact eventually_of_forall fun _ ↦ (integral_nonneg (fun _ ↦ statInfoFun_nonneg _ _ _))
    · refine (StronglyMeasurable.integral_prod_left ?_).aestronglyMeasurable
      exact (measurable_swap_iff.mpr h_meas).stronglyMeasurable
    congr with x
    rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall fun y ↦ statInfoFun_nonneg _ _ _)
      h_meas.of_uncurry_left.stronglyMeasurable.aestronglyMeasurable]
    refine ENNReal.ofReal_toReal <| (lintegral_ofReal_le_lintegral_nnnorm _).trans_lt ?_ |>.ne
    exact (integrable_statInfoFun 1 _).hasFiniteIntegral
  rw [int_eq_lint, lintegral_lintegral_swap h_meas.ennreal_ofReal.aemeasurable,
    integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact eventually_of_forall fun _ ↦ (integral_nonneg (fun _ ↦ statInfoFun_nonneg _ _ _))
  · exact h_meas.stronglyMeasurable.integral_prod_left.aestronglyMeasurable
  congr with γ
  rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall fun _ ↦ statInfoFun_nonneg _ _ _)
    h_meas.of_uncurry_right.stronglyMeasurable.aestronglyMeasurable, ENNReal.ofReal_toReal]
  have h_lt_top := (h_int' γ).hasFiniteIntegral
  simp_rw [HasFiniteIntegral, lt_top_iff_ne_top] at h_lt_top
  convert h_lt_top
  rw [← ENNReal.toReal_eq_toReal ENNReal.ofReal_ne_top ENNReal.coe_ne_top, toReal_coe_nnnorm,
    ENNReal.toReal_ofReal (statInfoFun_nonneg _ _ _),
    Real.norm_of_nonneg (statInfoFun_nonneg _ _ _)]

end CurvatureMeasure

end ProbabilityTheory

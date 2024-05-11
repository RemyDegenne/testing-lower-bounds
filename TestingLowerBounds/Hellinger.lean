/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.FDiv.Basic

/-!
# Helliger divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details

-/

open Real MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

-- todo: rename and move.
lemma integral_rpow_rnDeriv (ha_pos : 0 < a) (ha : a ≠ 1) [SigmaFinite μ] [SigmaFinite ν] :
    ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν = ∫ x, ((∂ν/∂μ) x).toReal ^ (1 - a) ∂μ := by
  let p := ∂μ/∂(μ + ν)
  let q := ∂ν/∂(μ + ν)
  calc ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν
    = ∫ x, ((p/q) x).toReal ^ a ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_eq_div μ ν] with x hx
        simp only [hx, Pi.div_apply, p, q]
  _ = ∫ x, (q x).toReal * ((p/q) x).toReal ^ a ∂(μ + ν) := by
        rw [← integral_rnDeriv_smul (_ : ν ≪ μ + ν)]
        · simp
        · rw [add_comm]
          exact Measure.AbsolutelyContinuous.rfl.add_right μ
  _ = ∫ x, (p x).toReal * ((q/p) x).toReal ^ (1 - a) ∂(μ + ν) := by
        refine integral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_lt_top μ (μ + ν), Measure.rnDeriv_lt_top ν (μ + ν)]
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
        filter_upwards [Measure.rnDeriv_eq_div ν μ] with x hx
        rw [add_comm] at hx
        simp only [hx, Pi.div_apply, p, q]

section HellingerFun

noncomputable
def hellingerFun (a : ℝ) : ℝ → ℝ := fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)

lemma continuous_rpow_const (ha_pos : 0 < a) : Continuous fun (x : ℝ) ↦ x ^ a := by
  rw [continuous_iff_continuousAt]
  exact fun _ ↦ continuousAt_rpow_const _ _ (Or.inr ha_pos)

lemma continuous_hellingerFun (ha_pos : 0 < a) : Continuous (hellingerFun a) :=
  continuous_const.mul ((continuous_rpow_const ha_pos).sub continuous_const)

lemma stronglyMeasurable_hellingerFun (ha_pos : 0 < a) : StronglyMeasurable (hellingerFun a) :=
  (continuous_hellingerFun ha_pos).stronglyMeasurable

@[simp]
lemma hellingerFun_one_eq_zero : hellingerFun a 1 = 0 := by simp [hellingerFun]

lemma convexOn_hellingerFun (ha_pos : 0 < a) : ConvexOn ℝ (Set.Ici 0) (hellingerFun a) := by
  cases le_total a 1 with
  | inl ha =>
    have : hellingerFun a = - (fun x ↦ (1 - a)⁻¹ * (x ^ a - 1)) := by
      ext x
      simp only [Pi.neg_apply]
      rw [← neg_mul, neg_inv, neg_sub, hellingerFun]
    rw [this]
    refine ConcaveOn.neg ?_
    have h : ConcaveOn ℝ (Set.Ici 0) fun x : ℝ ↦ x ^ a := by
      sorry
    simp_rw [← smul_eq_mul]
    exact ConcaveOn.smul (by simp [ha]) (h.sub (convexOn_const _ (convex_Ici 0)))
  | inr ha =>
    have h := convexOn_rpow ha
    unfold hellingerFun
    simp_rw [← smul_eq_mul]
    refine ConvexOn.smul (by simp [ha]) ?_
    exact h.sub (concaveOn_const _ (convex_Ici 0))

lemma tendsto_hellingerFun_div_atTop_of_one_lt (ha : 1 < a) :
    Tendsto (fun x ↦ hellingerFun a x / x) atTop atTop := by
  sorry

lemma tendsto_hellingerFun_div_atTop_of_lt_one (ha_pos : 0 < a) (ha : a < 1) :
    Tendsto (fun x ↦ hellingerFun a x / x) atTop (𝓝 0) := by
  sorry

lemma derivAtTop_hellingerFun_of_one_lt (ha : 1 < a) : derivAtTop (hellingerFun a) = ⊤ := by
  rw [derivAtTop, if_pos]
  exact tendsto_hellingerFun_div_atTop_of_one_lt ha

lemma derivAtTop_hellingerFun_of_lt_one (ha_pos : 0 < a) (ha : a < 1) :
    derivAtTop (hellingerFun a) = 0 :=
  derivAtTop_of_tendsto (tendsto_hellingerFun_div_atTop_of_lt_one ha_pos ha)

lemma integrable_hellingerFun_iff_integrable_rpow [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha : a ≠ 1) :
    Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν := by
  simp_rw [hellingerFun]
  rw [integrable_const_mul_iff]
  swap; · simp [sub_eq_zero, ha]
  simp_rw [sub_eq_add_neg, integrable_add_const_iff]

lemma integrable_hellingerFun_rnDeriv_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha : a < 1) :
    Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  refine integrable_f_rnDeriv_of_derivAtTop_ne_top μ ν ?_ ?_ ?_
  · exact stronglyMeasurable_hellingerFun ha_pos
  · exact convexOn_hellingerFun ha_pos
  · rw [derivAtTop_hellingerFun_of_lt_one ha_pos ha]
    exact EReal.zero_ne_top

lemma integrable_rpow_rnDeriv_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha : a < 1) :
    Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν := by
  rw [← integrable_hellingerFun_iff_integrable_rpow ha.ne]
  exact integrable_hellingerFun_rnDeriv_of_lt_one ha_pos ha

end HellingerFun

/-- Hellinger divergence of order `a`. Meaningful for `a ∈ (0, 1) ∪ (1, ∞)`. -/
noncomputable def hellingerDiv (a : ℝ) (μ ν : Measure α) : EReal := fDiv (hellingerFun a) μ ν

section TopAndBounds

lemma hellingerDiv_eq_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    hellingerDiv a μ ν = ⊤
      ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∨ ¬ μ ≪ ν := by
  simp [hellingerDiv, fDiv_eq_top_iff, derivAtTop_hellingerFun_of_one_lt ha]

lemma hellingerDiv_ne_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    hellingerDiv a μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν := by
  simp [hellingerDiv, fDiv_ne_top_iff, derivAtTop_hellingerFun_of_one_lt ha]

lemma hellingerDiv_eq_top_iff_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    hellingerDiv a μ ν = ⊤ ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  simp [hellingerDiv, fDiv_eq_top_iff, derivAtTop_hellingerFun_of_lt_one ha_pos ha]

lemma hellingerDiv_ne_top_iff_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    hellingerDiv a μ ν ≠ ⊤ ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  simp [hellingerDiv, fDiv_ne_top_iff, derivAtTop_hellingerFun_of_lt_one ha_pos ha]

lemma hellingerDiv_ne_top_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν ≠ ⊤ := by
  rw [hellingerDiv_ne_top_iff_of_lt_one ha_pos ha]
  exact integrable_hellingerFun_rnDeriv_of_lt_one ha_pos ha

lemma hellingerDiv_of_not_integrable [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_pos : 0 < a) (ha_ne_one : a ≠ 1)
    (h : ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    hellingerDiv a μ ν = ⊤ := by
  cases lt_or_gt_of_ne ha_ne_one with
  | inl h_lt => rwa [hellingerDiv_eq_top_iff_of_lt_one ha_pos h_lt]
  | inr h_gt =>
    rw [hellingerDiv_eq_top_iff_of_one_lt h_gt]
    exact Or.inl h

lemma hellingerDiv_le_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν ≤ (1 - a)⁻¹ * ν Set.univ := by
  rw [hellingerDiv]
  refine (fDiv_le_zero_add_top (stronglyMeasurable_hellingerFun ha_pos)
    (convexOn_hellingerFun ha_pos)).trans_eq ?_
  rw [derivAtTop_hellingerFun_of_lt_one ha_pos ha, hellingerFun, zero_rpow ha_pos.ne']
  simp only [zero_sub, mul_neg, mul_one, zero_mul, add_zero]
  rw [neg_inv, neg_sub]

end TopAndBounds

lemma hellingerDiv_eq_integral_of_integrable_of_ac
    (h : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν := by
  classical
  rw [hellingerDiv, fDiv_of_absolutelyContinuous hμν, if_pos h]

lemma hellingerDiv_eq_integral_of_ne_top [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) (h : hellingerDiv a μ ν ≠ ⊤) :
    hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν := by
  rw [hellingerDiv, fDiv_of_ne_top h]
  cases lt_or_gt_of_ne ha_ne_one with
  | inl ha_lt => rw [derivAtTop_hellingerFun_of_lt_one ha_pos ha_lt, zero_mul, add_zero]
  | inr ha_gt =>
    rw [hellingerDiv_ne_top_iff_of_one_lt ha_gt] at h
    rw [Measure.singularPart_eq_zero_of_ac h.2]
    simp

lemma hellingerDiv_eq_integral_of_ne_top' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) (h : hellingerDiv a μ ν ≠ ⊤) :
    hellingerDiv a μ ν = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ *  ν Set.univ := by
  rw [hellingerDiv_eq_integral_of_ne_top ha_pos ha_ne_one h]
  simp_rw [hellingerFun, integral_mul_left]
  rw [integral_sub _ (integrable_const _),
    integral_const, smul_eq_mul, mul_one, mul_sub, EReal.coe_sub, EReal.coe_mul, EReal.coe_mul,
    EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  rw [← integrable_hellingerFun_iff_integrable_rpow ha_ne_one]
  by_contra h_not_int
  exact h (hellingerDiv_of_not_integrable ha_pos ha_ne_one h_not_int)

lemma hellingerDiv_eq_integral_of_ne_top'' [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) (h : hellingerDiv a μ ν ≠ ⊤) :
    hellingerDiv a μ ν = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ := by
  rw [hellingerDiv_eq_integral_of_ne_top' ha_pos ha_ne_one h]
  simp

lemma hellingerDiv_eq_integral_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν :=
  hellingerDiv_eq_integral_of_ne_top ha_pos ha.ne (hellingerDiv_ne_top_of_lt_one ha_pos ha μ ν)

lemma hellingerDiv_eq_integral_of_lt_one' (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ *  ν Set.univ :=
  hellingerDiv_eq_integral_of_ne_top' ha_pos ha.ne (hellingerDiv_ne_top_of_lt_one ha_pos ha μ ν)

lemma hellingerDiv_symm' (ha_pos : 0 < a) (ha : a < 1) (h_eq : μ Set.univ = ν Set.univ)
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
    rw [← neg_neg (1 - a), neg_sub, neg_mul, mul_inv_cancel, inv_neg, mul_comm, neg_mul,
      inv_mul_cancel ha_pos.ne']
    linarith
  rw [integral_rpow_rnDeriv ha_pos ha.ne]
  congr

lemma hellingerDiv_symm (ha_pos : 0 < a) (ha : a < 1)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (1 - a) * hellingerDiv a μ ν = a * hellingerDiv (1 - a) ν μ :=
  hellingerDiv_symm' ha_pos ha (by simp)

end ProbabilityTheory

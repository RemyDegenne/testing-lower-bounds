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

section HellingerFun

noncomputable
def hellingerFun (a : ℝ) : ℝ → ℝ := fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)

lemma continuous_hellingerFun (ha_pos : 0 < a) : Continuous (hellingerFun a) := by
  refine continuous_const.mul (Continuous.sub ?_ continuous_const)
  rw [continuous_iff_continuousAt]
  exact fun _ ↦ continuousAt_rpow_const _ _ (Or.inr ha_pos)

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

lemma integrable_hellingerFun_rnDeriv_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha : a < 1) :
    Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  refine integrable_f_rnDeriv_of_derivAtTop_ne_top μ ν ?_ ?_ ?_
  · exact stronglyMeasurable_hellingerFun ha_pos
  · exact convexOn_hellingerFun ha_pos
  · rw [derivAtTop_hellingerFun_of_lt_one ha_pos ha]
    exact EReal.zero_ne_top

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

lemma hellingerDiv_eq_integral_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν := by
  have h := hellingerDiv_ne_top_of_lt_one ha_pos ha μ ν
  rw [hellingerDiv, fDiv_of_ne_top h, derivAtTop_hellingerFun_of_lt_one ha_pos ha, zero_mul,
    add_zero]

lemma hellingerDiv_eq_integral_of_lt_one' (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a - 1 ∂ν := by
  rw [hellingerDiv_eq_integral_of_lt_one ha_pos ha μ ν, ← EReal.coe_mul, ← integral_mul_left]
  rfl

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

lemma hellingerDiv_symm' (ha_pos : 0 < a) (ha : a < 1) (h_eq : μ Set.univ = ν Set.univ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (1 - a) * hellingerDiv a μ ν = a * hellingerDiv (1 - a) ν μ := by
  rw [hellingerDiv_eq_integral_of_lt_one' ha_pos ha, hellingerDiv_eq_integral_of_lt_one']
  rotate_left
  · linarith
  · linarith
  simp only [sub_sub_cancel_left]
  rw [← mul_assoc, ← mul_assoc]
  have : (1 - (a : EReal)) * ↑(a - 1)⁻¹ = -1 := by
    norm_cast
    rw [← neg_neg (1 - a), neg_sub, neg_mul, mul_inv_cancel]
    · simp
    · linarith
  rw [this, ← EReal.coe_mul, inv_neg, mul_neg, mul_inv_cancel ha_pos.ne']
  simp only [neg_mul, one_mul, EReal.coe_neg, EReal.coe_one, neg_inj, EReal.coe_eq_coe_iff]
  rw [integral_sub _ (integrable_const _), integral_sub _ (integrable_const _), integral_const,
    integral_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one, h_eq]
  rotate_left
  · sorry
  · sorry
  congr 1
  let p := ∂μ/∂(μ + ν)
  let q := ∂ν/∂(μ + ν)
  -- todo: should we use (∂μ/∂(μ+ν))/(∂ν/∂(μ+ν)) instead of ∂μ/∂ν everywhere?
  calc ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν
    = ∫ x, ((p/q) x).toReal ^ a ∂ν := sorry
  _ = ∫ x, ((q/p) x).toReal * ((p/q) x).toReal ^ a ∂(μ + ν) := sorry
  _ = ∫ x, ((q/p) x).toReal ^ (1 - a) ∂(μ + ν) := sorry
  _ = ∫ x, ((∂ν/∂μ) x).toReal ^ (1 - a) ∂μ := sorry

lemma hellingerDiv_symm (ha_pos : 0 < a) (ha : a < 1)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (1 - a) * hellingerDiv a μ ν = a * hellingerDiv (1 - a) ν μ :=
  hellingerDiv_symm' ha_pos ha (by simp)

end ProbabilityTheory

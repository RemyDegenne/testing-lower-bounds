/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.KullbackLeibler
import TestingLowerBounds.Hellinger
import Mathlib.Probability.Moments

/-!
# Rényi divergence

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

open Classical in
noncomputable def renyiDiv (a : ℝ) (μ ν : Measure α) : EReal :=
  if a = 0 then - log (ν {x | 0 < (∂μ/∂ν) x}).toReal
  else if a = 1 then kl μ ν
  else if hellingerDiv a μ ν ≠ ⊤
    then (a - 1)⁻¹ * log (1 + (a - 1) * (hellingerDiv a μ ν).toReal)
    else ⊤

@[simp]
lemma renyiDiv_zero (μ ν : Measure α) :
    renyiDiv 0 μ ν = - log (ν {x | 0 < (∂μ/∂ν) x}).toReal := if_pos rfl

@[simp]
lemma renyiDiv_one (μ ν : Measure α) : renyiDiv 1 μ ν = kl μ ν := by
  rw [renyiDiv, if_neg (by simp), if_pos rfl]

section TopAndBounds

lemma renyiDiv_eq_top_iff_hellingerDiv_eq_top [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) :
    renyiDiv a μ ν = ⊤ ↔ hellingerDiv a μ ν = ⊤ := by
  simp only [renyiDiv, ha_pos.ne', ↓reduceIte, ha_ne_one, ne_eq, ite_not, ite_eq_left_iff]
  rw [← EReal.coe_mul]
  simp only [EReal.coe_ne_top, imp_false, not_not]

lemma renyiDiv_eq_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    renyiDiv a μ ν = ⊤
      ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∨ ¬ μ ≪ ν := by
  rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top (zero_lt_one.trans ha) ha.ne',
    hellingerDiv_eq_top_iff_of_one_lt ha]

lemma renyiDiv_ne_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    renyiDiv a μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν := by
  rw [ne_eq, renyiDiv_eq_top_iff_hellingerDiv_eq_top (zero_lt_one.trans ha) ha.ne',
    hellingerDiv_eq_top_iff_of_one_lt ha]
  push_neg
  rfl

lemma renyiDiv_eq_top_iff_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    renyiDiv a μ ν = ⊤ ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top ha_pos ha.ne,
    hellingerDiv_eq_top_iff_of_lt_one ha_pos ha]

lemma renyiDiv_ne_top_iff_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    renyiDiv a μ ν ≠ ⊤ ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  rw [ne_eq, renyiDiv_eq_top_iff_hellingerDiv_eq_top ha_pos ha.ne,
    hellingerDiv_eq_top_iff_of_lt_one ha_pos ha]
  push_neg
  rfl

lemma renyiDiv_ne_top_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν ≠ ⊤ := by
  rw [ne_eq, renyiDiv_eq_top_iff_hellingerDiv_eq_top ha_pos ha.ne]
  exact hellingerDiv_ne_top_of_lt_one ha_pos ha _ _

lemma renyiDiv_of_not_integrable [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_pos : 0 < a) (ha_ne_one : a ≠ 1)
    (h_int : ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    renyiDiv a μ ν = ⊤ := by
  rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top ha_pos ha_ne_one]
  by_contra h
  exact h (hellingerDiv_of_not_integrable ha_pos ha_ne_one h_int)

lemma renyiDiv_of_lt_one' [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_pos : 0 < a) (ha_lt_one : a < 1)
    (h_int : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    renyiDiv a μ ν = (a - 1)⁻¹ * log (1 + (a - 1) * (hellingerDiv a μ ν).toReal) := by
  rw [renyiDiv, if_neg ha_pos.ne', if_neg ha_lt_one.ne,
    if_pos ((hellingerDiv_ne_top_iff_of_lt_one ha_pos ha_lt_one _ _).mpr h_int)]

lemma renyiDiv_of_lt_one (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_lt_one : a < 1) :
    renyiDiv a μ ν = (a - 1)⁻¹ * log (1 + (a - 1) * (hellingerDiv a μ ν).toReal) := by
  rw [renyiDiv_of_lt_one' ha_pos ha_lt_one]
  exact integrable_hellingerFun_rnDeriv_of_lt_one ha_pos ha_lt_one

lemma renyiDiv_of_one_lt_of_ac [IsFiniteMeasure μ] [SigmaFinite ν] (ha_one_lt : 1 < a)
    (h_int : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    renyiDiv a μ ν = (a - 1)⁻¹ * log (1 + (a - 1) * (hellingerDiv a μ ν).toReal) := by
  rw [renyiDiv, if_neg (zero_lt_one.trans ha_one_lt).ne', if_neg ha_one_lt.ne',
    if_pos ((hellingerDiv_ne_top_iff_of_one_lt ha_one_lt _ _).mpr ⟨h_int, hμν⟩)]

lemma renyiDiv_of_one_lt_of_not_ac [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_one_lt : 1 < a) (hμν : ¬ μ ≪ ν) :
    renyiDiv a μ ν = ⊤ := by
  rw [renyiDiv, if_neg (zero_lt_one.trans ha_one_lt).ne', if_neg ha_one_lt.ne', if_neg]
  rw [hellingerDiv_ne_top_iff_of_one_lt ha_one_lt]
  push_neg
  exact fun _ ↦ hμν

end TopAndBounds

section IntegralForm

/-- The Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `ν`. -/
lemma renyiDiv_eq_log_integral [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (ha_pos : 0 < a) (ha : a < 1) :
    renyiDiv a μ ν = (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν) := by
  rw [renyiDiv_of_lt_one μ ν ha_pos ha]
  congr
  rw [hellingerDiv_eq_integral_of_lt_one' ha_pos ha]
  simp only [measure_univ, EReal.coe_ennreal_one, mul_one]
  rw [EReal.toReal_sub, EReal.toReal_mul, EReal.toReal_coe, EReal.toReal_coe, mul_sub, ← mul_assoc,
    mul_inv_cancel, one_mul]
  · simp
  · linarith
  · rw [← EReal.coe_mul]
    exact EReal.coe_ne_top _
  · rw [← EReal.coe_mul]
    exact EReal.coe_ne_bot _
  · exact EReal.coe_ne_top _
  · exact EReal.coe_ne_bot _

/-- The Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `ν`.
If `a < 1`, use `renyiDiv_eq_log_integral` instead. -/
lemma renyiDiv_eq_log_integral_of_ne_top [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (ha_pos : 0 < a) (ha : a ≠ 1) (h : renyiDiv a μ ν ≠ ⊤) :
    renyiDiv a μ ν = (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν) := by
  cases lt_or_gt_of_ne ha with
  | inl ha => exact renyiDiv_eq_log_integral ha_pos ha
  | inr ha =>
    have h_ne_top : hellingerDiv a μ ν ≠ ⊤ := by
      rwa [ne_eq, ← renyiDiv_eq_top_iff_hellingerDiv_eq_top ha_pos ha.ne']
    rw [renyiDiv_ne_top_iff_of_one_lt ha] at h
    rw [renyiDiv_of_one_lt_of_ac ha h.1 h.2]
    congr
    rw [hellingerDiv_eq_integral_of_ne_top'' ha_pos ha.ne' h_ne_top]
    rw [EReal.toReal_sub, EReal.toReal_mul, EReal.toReal_coe, EReal.toReal_coe, mul_sub, ← mul_assoc,
      mul_inv_cancel, one_mul]
    · simp
    · linarith
    · rw [← EReal.coe_mul]
      exact EReal.coe_ne_top _
    · rw [← EReal.coe_mul]
      exact EReal.coe_ne_bot _
    · exact EReal.coe_ne_top _
    · exact EReal.coe_ne_bot _

/-- If `μ ≪ ν`, the Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `μ`. -/
lemma renyiDiv_eq_log_integral' [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (ha_pos : 0 < a) (ha : a < 1) (hμν : μ ≪ ν) :
    renyiDiv a μ ν = (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x).toReal ^ (a - 1) ∂μ) := by
  rw [renyiDiv_eq_log_integral ha_pos ha, integral_rpow_rnDeriv ha_pos ha.ne]
  congr 3
  refine integral_congr_ae ?_
  filter_upwards [Measure.inv_rnDeriv hμν] with x hx
  rw [← hx, Pi.inv_apply, ENNReal.toReal_inv, inv_rpow ENNReal.toReal_nonneg,
    ← rpow_neg ENNReal.toReal_nonneg, neg_sub]

/-- If `μ ≪ ν`, the Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `μ`.
If `a < 1`, use `renyiDiv_eq_log_integral'` instead. -/
lemma renyiDiv_eq_log_integral_of_ne_top' [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (ha_pos : 0 < a) (ha : a ≠ 1) (hμν : μ ≪ ν) (h : renyiDiv a μ ν ≠ ⊤) :
    renyiDiv a μ ν = (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x).toReal ^ (a - 1) ∂μ) := by
  rw [renyiDiv_eq_log_integral_of_ne_top ha_pos ha, integral_rpow_rnDeriv ha_pos ha]
  congr 3
  refine integral_congr_ae ?_
  filter_upwards [Measure.inv_rnDeriv hμν] with x hx
  rw [← hx, Pi.inv_apply, ENNReal.toReal_inv, inv_rpow ENNReal.toReal_nonneg,
    ← rpow_neg ENNReal.toReal_nonneg, neg_sub]
  congr

end IntegralForm

lemma renyiDiv_symm' (ha_pos : 0 < a) (ha : a < 1) (h_eq : μ Set.univ = ν Set.univ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (1 - a) * renyiDiv a μ ν = a * renyiDiv (1 - a) ν μ := by
  rw [renyiDiv_of_lt_one _ _ ha_pos ha, renyiDiv_of_lt_one _ _]
  rotate_left
  · linarith
  · linarith
  simp only [sub_sub_cancel_left, neg_mul]
  rw [← mul_assoc, ← mul_assoc]
  have h : (1 - a) * hellingerDiv a μ ν = a * hellingerDiv (1 - a) ν μ :=
    hellingerDiv_symm' ha_pos ha h_eq
  have : (1 - (a : EReal)) * ↑(a - 1)⁻¹ = -1 := by
    norm_cast
    rw [← neg_neg (1 - a), neg_sub, neg_mul, mul_inv_cancel]
    · simp
    · linarith
  rw [this, ← EReal.coe_mul, inv_neg, mul_neg, mul_inv_cancel ha_pos.ne']
  simp only [EReal.coe_neg, EReal.coe_one, one_mul]
  congr
  rw [← EReal.toReal_coe a, ← EReal.toReal_mul, EReal.toReal_coe a, ← h, EReal.toReal_mul,
    ← neg_mul]
  congr
  norm_cast
  rw [EReal.toReal_coe, neg_sub]

lemma renyiDiv_symm [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ha_pos : 0 < a) (ha : a < 1) :
    (1 - a) * renyiDiv a μ ν = a * renyiDiv (1 - a) ν μ :=
  renyiDiv_symm' ha_pos ha (by simp)

-- todo: `ν ≪ μ` is necessary (?) due to the llr being 0 when `(∂μ/∂ν) x = 0`.
-- In that case, `exp (llr μ ν x) = 1 ≠ 0 = (∂μ/∂ν) x`.
lemma cgf_llr [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ)
    (ha_pos : 0 < a) (ha : a < 1) :
    cgf (llr μ ν) ν a = (a - 1) * renyiDiv a μ ν := by
  rw [renyiDiv_eq_log_integral ha_pos ha, ← mul_assoc]
  have : ((a : EReal) - 1) * ↑(a - 1)⁻¹ = 1 := by
    norm_cast
    rw [mul_inv_cancel]
    linarith
  rw [this, one_mul, cgf, mgf]
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top μ ν, Measure.rnDeriv_pos' hνμ] with x hx_lt_top hx_pos
  rw [llr_def]
  simp only
  have h_pos : 0 < ((∂μ/∂ν) x).toReal :=  ENNReal.toReal_pos hx_pos.ne' hx_lt_top.ne
  rw [← log_rpow h_pos, exp_log (rpow_pos_of_pos h_pos _)]

lemma cgf_llr' [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (ha_pos : 0 < a) (h : renyiDiv (1 + a) μ ν ≠ ⊤) :
    cgf (llr μ ν) μ a = a * renyiDiv (1 + a) μ ν := by
  have hμν : μ ≪ ν := by
    rw [renyiDiv_ne_top_iff_of_one_lt] at h
    · exact h.2
    · linarith
  rw [renyiDiv_eq_log_integral_of_ne_top' _ _ hμν h, ← mul_assoc]
  rotate_left
  · linarith
  · linarith
  simp only [add_sub_cancel_left]
  have : (a : EReal) * ↑a⁻¹ = 1 := by
    norm_cast
    rw [mul_inv_cancel]
    linarith
  rw [this, one_mul, cgf, mgf]
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [hμν <| Measure.rnDeriv_lt_top μ ν, Measure.rnDeriv_pos hμν]
    with x hx_lt_top hx_pos
  rw [llr_def]
  simp only
  have h_pos : 0 < ((∂μ/∂ν) x).toReal :=  ENNReal.toReal_pos hx_pos.ne' hx_lt_top.ne
  rw [← log_rpow h_pos, exp_log (rpow_pos_of_pos h_pos _)]

section RenyiMeasure

/-- Density of the Rényi measure `renyiMeasure a μ ν` with respect to `μ + ν`. -/
noncomputable
def renyiDensity (a : ℝ) (μ ν : Measure α) (x : α) : ℝ≥0∞ :=
  ((∂μ/∂(μ + ν)) x) ^ a * ((∂ν/∂(μ + ν)) x) ^ (1 - a)
    * ENNReal.ofReal (exp ((a - 1) * (renyiDiv a μ ν).toReal))

/-- Tilted measure of `μ` with respect to `ν` parametrized by `a`. -/
noncomputable
def renyiMeasure (a : ℝ) (μ ν : Measure α) : Measure α :=
  (μ + ν).withDensity (renyiDensity a μ ν)

end RenyiMeasure

end ProbabilityTheory

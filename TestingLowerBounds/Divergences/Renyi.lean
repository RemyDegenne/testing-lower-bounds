/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.Hellinger
import Mathlib.Probability.Moments
import Mathlib.Data.Real.Sign
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Rényi divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation


## Implementation details


-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α} {a : ℝ}

-- todo: move
lemma exp_mul_llr [SigmaFinite μ] [SigmaFinite ν] (hνμ : ν ≪ μ) :
    (fun x ↦ exp (a * llr μ ν x)) =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toReal ^ a := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν, Measure.rnDeriv_pos' hνμ] with x hx_lt_top hx_pos
  simp only [llr_def]
  have h_pos : 0 < ((∂μ/∂ν) x).toReal :=  ENNReal.toReal_pos hx_pos.ne' hx_lt_top.ne
  rw [← log_rpow h_pos, exp_log (rpow_pos_of_pos h_pos _)]

-- todo: move
lemma exp_mul_llr' [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (fun x ↦ exp (a * llr μ ν x)) =ᵐ[μ] fun x ↦ (μ.rnDeriv ν x).toReal ^ a := by
  filter_upwards [hμν <| Measure.rnDeriv_lt_top μ ν, Measure.rnDeriv_pos hμν]
    with x hx_lt_top hx_pos
  simp only [llr_def]
  have h_pos : 0 < ((∂μ/∂ν) x).toReal :=  ENNReal.toReal_pos hx_pos.ne' hx_lt_top.ne
  rw [← log_rpow h_pos, exp_log (rpow_pos_of_pos h_pos _)]

lemma integrable_rpow_rnDeriv_compProd_right_iff [CountableOrCountablyGenerated α β]
    (ha_pos : 0 < a) (ha_one : a ≠ 1) (κ η : Kernel α β) (μ : Measure α)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
    (h_ac : 1 ≤ a → ∀ᵐ (x : α) ∂μ, κ x ≪ η x) :
    Integrable (fun x ↦ ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal ^ a) (μ ⊗ₘ η)
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
        ∧ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂(η x)) μ := by
  simp_rw [← integrable_hellingerFun_iff_integrable_rpow ha_one,
    integrable_f_rnDeriv_compProd_right_iff (stronglyMeasurable_hellingerFun (by linarith))
    (convexOn_hellingerFun (by linarith))]
  refine and_congr_right (fun h_int ↦ ?_)
  rw [← integrable_hellingerDiv_iff h_int h_ac]
  refine integrable_hellingerDiv_iff' ha_pos ha_one ?_ h_ac
  simp_rw [← integrable_hellingerFun_iff_integrable_rpow ha_one, h_int]

/-- Rényi divergence of order `a`. If `a = 1`, it is defined as `kl μ ν`, otherwise as
`(a - 1)⁻¹ * log (ν(α) + (a - 1) * Hₐ(μ, ν))`.
If `ν` is a probability measure then this becomes the more usual definition
`(a - 1)⁻¹ * log (1 + (a - 1) * Hₐ(μ, ν))`, but this definition maintains some useful properties
also for a general finite measure `ν`, in particular the integral form
`Rₐ(μ, ν) = (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x) ^ a ∂ν)`.
We use ENNReal.log instead of Real.log, because it is monotone on `ℝ≥0∞`, while the real log is
monotone only on `(0, ∞)` (`Real.log 0 = 0`). This allows us to transfer inequalities from the
Hellinger divergence to the Rényi divergence. -/

noncomputable def renyiDiv (a : ℝ) (μ ν : Measure α) : EReal :=
  if a = 1 then kl μ ν
  else (a - 1)⁻¹ * ENNReal.log ((↑(ν Set.univ) + (a - 1) * (hellingerDiv a μ ν)).toENNReal)

@[simp]
lemma renyiDiv_zero (μ ν : Measure α) [SigmaFinite μ] [IsFiniteMeasure ν] :
    renyiDiv 0 μ ν = - ENNReal.log (ν {x | 0 < (∂μ/∂ν) x}) := by
  rw [renyiDiv, if_neg zero_ne_one]
  simp only [zero_sub, ← neg_inv, inv_one, EReal.coe_neg, EReal.coe_one, EReal.coe_zero, neg_mul,
    one_mul, ← sub_eq_add_neg, neg_inj]
  congr
  rw [hellingerDiv_zero'', sub_eq_add_neg, EReal.neg_sub, ← add_assoc, ← sub_eq_add_neg,
    EReal.sub_self, zero_add, EReal.toENNReal_coe]
    <;> simp only [ne_eq, EReal.coe_ennreal_eq_top_iff, EReal.coe_ennreal_ne_bot,measure_ne_top,
      not_false_eq_true, or_self]

@[simp]
lemma renyiDiv_one (μ ν : Measure α) : renyiDiv 1 μ ν = kl μ ν := by
  rw [renyiDiv, if_pos rfl]

lemma renyiDiv_of_ne_one (ha_ne_one : a ≠ 1) (μ ν : Measure α) :
    renyiDiv a μ ν
      = (a - 1)⁻¹ * ENNReal.log ((↑(ν Set.univ) + (a - 1) * (hellingerDiv a μ ν)).toENNReal) := by
  rw [renyiDiv, if_neg ha_ne_one]

@[simp]
lemma renyiDiv_zero_measure_left (ν : Measure α) [IsFiniteMeasure ν] :
    renyiDiv a 0 ν = sign (a - 1) * ⊥ := by
  by_cases ha : a = 1
  · simp [ha]
  rw_mod_cast [renyiDiv_of_ne_one ha, hellingerDiv_zero_measure_left, ← mul_assoc, ← neg_sub a 1,
    ← neg_inv, ← neg_mul_eq_mul_neg, mul_inv_cancel (sub_ne_zero.mpr ha)]
  simp only [EReal.coe_neg, EReal.coe_one, neg_mul, one_mul, ← sub_eq_add_neg,
    EReal.sub_self_le_zero, EReal.toENNReal_of_nonpos, ENNReal.log_zero]
  rcases lt_or_gt_of_ne ha with (ha | ha)
  · simp [sub_neg.mpr ha, Real.sign_of_neg, EReal.mul_bot_of_neg]
  · simp [sub_pos.mpr ha, Real.sign_of_pos, EReal.mul_bot_of_pos]

@[simp]
lemma renyiDiv_zero_measure_right (μ : Measure α) [NeZero μ] :
    renyiDiv a μ 0 = ⊤ := by
  rcases lt_trichotomy a 1 with (ha | rfl | ha)
  · rw [renyiDiv_of_ne_one ha.ne, hellingerDiv_zero_measure_right_of_lt_one ha]
    simp [sub_neg.mpr ha, Real.sign_of_neg, EReal.mul_bot_of_neg]
  · simp
  · rw [renyiDiv_of_ne_one ha.ne', hellingerDiv_zero_measure_right_of_one_le ha.le,
      EReal.mul_top_of_pos (by exact_mod_cast sub_pos.mpr ha)]
    simp only [Measure.coe_zero, Pi.zero_apply, EReal.coe_ennreal_zero, zero_add,
      EReal.toENNReal_top, ENNReal.log_top]
    rw [EReal.mul_top_of_pos]
    simp [ha]

section RenyiEq

lemma renyiDiv_eq_top_of_hellingerDiv_eq_top' (ha_ne_one : a ≠ 1) (h : hellingerDiv a μ ν = ⊤) :
    renyiDiv a μ ν = ⊤ := by
  rw [renyiDiv, if_neg ha_ne_one]
  rcases lt_or_gt_of_ne ha_ne_one with (ha | ha)
  · rw [h, EReal.mul_top_of_neg, EReal.add_bot, EReal.toENNReal_of_nonpos bot_le, ENNReal.log_zero,
      EReal.mul_bot_of_neg]
      <;> norm_cast <;> simp [ha]
  · rw [h, EReal.mul_top_of_pos, EReal.add_top_of_ne_bot (EReal.coe_ennreal_ne_bot _), EReal.toENNReal_top,
      ENNReal.log_top, EReal.mul_top_of_pos]
      <;> norm_cast <;> simp [ha]

lemma renyiDiv_eq_top_of_hellingerDiv_eq_top [SigmaFinite μ] [SigmaFinite ν]
    (h : hellingerDiv a μ ν = ⊤) :
    renyiDiv a μ ν = ⊤ := by
  by_cases ha : a = 1
  · rw [← h, ha, renyiDiv_one, hellingerDiv_one]
  · exact renyiDiv_eq_top_of_hellingerDiv_eq_top' ha h

lemma renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_lt (ha : 1 < a) [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ⊤ ↔ hellingerDiv a μ ν = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ renyiDiv_eq_top_of_hellingerDiv_eq_top' ha.ne' h⟩
  contrapose! h
  rw [renyiDiv_of_ne_one ha.ne']
  apply (EReal.mul_eq_top _ _).mp.mt
  simp only [EReal.coe_ne_bot, false_and, EReal.coe_neg', inv_lt_zero, sub_neg, not_lt_of_gt ha,
    EReal.coe_ne_top, EReal.coe_pos, inv_pos, sub_pos, ha, ENNReal.log_eq_top_iff,
    EReal.toENNReal_eq_top_iff, true_and, false_or]
  apply EReal.add_ne_top
  · simp [measure_ne_top]
  · apply (EReal.mul_eq_top _ _).mp.mt
    simp only [h, and_false, or_false, not_or, not_and, not_lt]
    have h1 : a.toEReal - 1 ≥ 0 := by
      norm_cast
      simp only [sub_nonneg, ha.le]
    have h2 : a.toEReal - 1 ≠ ⊥ := by
      intro _
      simp_all only [le_bot_iff, EReal.zero_ne_bot]
    have h3 : a.toEReal - 1 ≠ ⊤ := mod_cast EReal.coe_ne_top _
    simp [h1, h2, h3]

lemma renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le (ha : 1 ≤ a)
    [SigmaFinite μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ⊤ ↔ hellingerDiv a μ ν = ⊤ := by
  by_cases ha_one : a = 1
  · rw [ha_one, renyiDiv_one, hellingerDiv_one]
  · exact renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_lt
      (lt_of_le_of_ne ha fun h ↦ ha_one h.symm)

lemma renyiDiv_eq_top_iff_of_one_lt (ha : 1 < a) [SigmaFinite μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ⊤ ↔ ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∨ ¬ μ ≪ ν := by
  simp_rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le ha.le,
    ← integrable_hellingerFun_iff_integrable_rpow ha.ne', hellingerDiv_eq_top_iff, ha.le, true_and]

lemma renyiDiv_ne_top_iff_of_one_lt (ha : 1 < a) [SigmaFinite μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν ≠ ⊤ ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∧ μ ≪ ν := by
  rw [ne_eq, renyiDiv_eq_top_iff_of_one_lt ha]
  simp

lemma renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ⊤ ↔ μ ⟂ₘ ν := by
  rw [renyiDiv_of_ne_one ha.ne, EReal.mul_eq_top,
    ← toENNReal_meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_lt_one ha_nonneg ha]
  simp [ha, not_lt_of_gt ha]

lemma renyiDiv_ne_bot_of_le_one (ha : a ≤ 1) [IsFiniteMeasure ν] :
    renyiDiv a μ ν ≠ ⊥ := by
  by_cases ha_one : a = 1
  · rw [ha_one, renyiDiv_one]
    exact kl_ne_bot μ ν
  replace ha : a < 1 := lt_of_le_of_ne ha ha_one
  rw [renyiDiv_of_ne_one ha_one, ne_eq, EReal.mul_eq_bot]
  simp only [EReal.coe_ne_bot, false_and, EReal.coe_pos, inv_pos, sub_pos, not_lt_of_gt ha,
    EReal.coe_ne_top, EReal.coe_neg', inv_lt_zero, sub_neg, ha, ENNReal.log_eq_top_iff,
    EReal.toENNReal_eq_top_iff, true_and, false_or]
  exact meas_univ_add_mul_hellingerDiv_ne_top_of_lt_one ha

lemma renyiDiv_eq_bot_iff_of_one_lt (ha : 1 < a) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ⊥ ↔ μ = 0 := by
  rw [renyiDiv_of_ne_one ha.ne', EReal.mul_eq_bot]
  simp only [EReal.coe_ne_bot, false_and, EReal.coe_pos, inv_pos, sub_pos, ha, ENNReal.log_eq_bot_iff,
    true_and, EReal.coe_ne_top, EReal.coe_neg', inv_lt_zero, sub_neg, not_lt_of_gt ha,
    ENNReal.log_eq_top_iff, EReal.toENNReal_eq_top_iff, or_self, or_false, false_or]
  exact toENNReal_meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_one_lt ha

lemma renyiDiv_ne_bot [hμ : NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν ≠ ⊥ := by
  rcases le_or_lt a 1 with (ha | ha)
  · exact renyiDiv_ne_bot_of_le_one ha
  · exact (renyiDiv_eq_bot_iff_of_one_lt ha).mp.mt hμ.out

/- TODO: it may be possible to handle also the cases where `ν` is infinite in many of the lemmas
in this section, since in this case, if `a < 1`, then `Rₐ(μ, ν) = ⊥`, it is likely possible to
prove similar properties in the case where `1 < a`. Maybe something similar is possible also for
`μ`, but for now I'm not sure how. -/

lemma renyiDiv_of_mutuallySingular (ha_nonneg : 0 ≤ a) [NeZero μ]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ⟂ₘ ν) :
    renyiDiv a μ ν = ⊤ := by
  by_cases ha : a < 1
  · rw [renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_nonneg ha]
    exact hμν
  · rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le (le_of_not_lt ha)]
    exact hellingerDiv_of_mutuallySingular_of_one_le (le_of_not_lt ha) hμν

lemma renyiDiv_of_one_lt_of_not_integrable (ha : 1 < a) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_int : ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) :
    renyiDiv a μ ν = ⊤ := by
  rw [renyiDiv_eq_top_iff_of_one_lt ha]
  exact Or.inl h_int

lemma renyiDiv_of_one_le_of_not_ac (ha : 1 ≤ a) (h_ac : ¬ μ ≪ ν)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ⊤ := by
  by_cases ha_one : a = 1
  · rw [ha_one, renyiDiv_one]
    exact kl_of_not_ac h_ac
  replace ha : 1 < a := lt_of_le_of_ne ha fun h ↦ ha_one h.symm
  rw [renyiDiv_eq_top_iff_of_one_lt ha]
  exact Or.inr h_ac

end RenyiEq

lemma forall_renyiDiv_eq_top_of_eq_top_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) [NeZero μ]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : renyiDiv a μ ν = ⊤) :
    ∀ a', 0 ≤ a' → renyiDiv a' μ ν = ⊤ := by
  rw [renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_nonneg ha] at h
  exact fun _ ha' ↦ renyiDiv_of_mutuallySingular ha' h

section IntegralForm

/-- The Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `ν`. -/
lemma renyiDiv_eq_log_integral_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = (a - 1)⁻¹ * ENNReal.log (ENNReal.ofReal (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν)) := by
  rw [renyiDiv_of_ne_one ha.ne, meas_univ_add_mul_hellingerDiv_eq ha_pos.ne' ha.ne]
  · rfl
  · exact hellingerDiv_ne_top_of_lt_one ha_pos.le ha _ _

/-- The Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `ν`.
If `a < 1`, use `renyiDiv_eq_log_integral_of_lt_one` instead. -/
lemma renyiDiv_eq_log_integral (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) (h_ac : μ ≪ ν) :
    renyiDiv a μ ν = (a - 1)⁻¹ * ENNReal.log (ENNReal.ofReal (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν)) := by
  rw [renyiDiv_of_ne_one ha_ne_one, meas_univ_add_mul_hellingerDiv_eq (by linarith) ha_ne_one]
  · rfl
  rcases lt_or_gt_of_ne ha_ne_one with (ha | ha)
  · exact hellingerDiv_ne_top_of_lt_one ha_pos.le ha _ _
  · exact (hellingerDiv_ne_top_iff_of_one_lt ha _ _).mpr ⟨h_int, h_ac⟩

/-- If `μ ≪ ν`, the Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `μ`. -/
lemma renyiDiv_eq_log_integral_of_lt_one' (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
    renyiDiv a μ ν
      = (a - 1)⁻¹ * ENNReal.log (ENNReal.ofReal (∫ x, ((∂μ/∂ν) x).toReal ^ (a - 1) ∂μ)) := by
  rw [renyiDiv_eq_log_integral_of_lt_one ha_pos ha, integral_rpow_rnDeriv ha_pos ha.ne]
  congr 3
  refine integral_congr_ae ?_
  filter_upwards [Measure.inv_rnDeriv h_ac] with x hx
  rw [← hx, Pi.inv_apply, ENNReal.toReal_inv, inv_rpow ENNReal.toReal_nonneg,
    ← rpow_neg ENNReal.toReal_nonneg, neg_sub]

/-- If `μ ≪ ν`, the Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `μ`.
If `a < 1`, use `renyiDiv_eq_log_integral_of_lt_one'` instead. -/
lemma renyiDiv_eq_log_integral' (ha_pos : 0 < a) (ha : a ≠ 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) (h_ac : μ ≪ ν) :
    renyiDiv a μ ν
      = (a - 1)⁻¹ * ENNReal.log (ENNReal.ofReal (∫ x, ((∂μ/∂ν) x).toReal ^ (a - 1) ∂μ)) := by
  rw [renyiDiv_eq_log_integral ha_pos ha h_int h_ac, integral_rpow_rnDeriv ha_pos ha]
  congr 3
  refine integral_congr_ae ?_
  filter_upwards [Measure.inv_rnDeriv h_ac] with x hx
  rw [← hx, Pi.inv_apply, ENNReal.toReal_inv, inv_rpow ENNReal.toReal_nonneg,
    ← rpow_neg ENNReal.toReal_nonneg, neg_sub]

end IntegralForm

lemma renyiDiv_symm' (ha_pos : 0 < a) (ha : a < 1) (h_eq : μ Set.univ = ν Set.univ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (1 - a) * renyiDiv a μ ν = a * renyiDiv (1 - a) ν μ := by
  rw [renyiDiv_of_ne_one ha.ne, renyiDiv_of_ne_one (by linarith)]
  simp only [sub_sub_cancel_left, neg_mul]
  rw [← mul_assoc, ← mul_assoc]
  have h : (1 - a) * hellingerDiv a μ ν = a * hellingerDiv (1 - a) ν μ :=
    hellingerDiv_symm' ha_pos ha h_eq
  have : (1 - (a : EReal)) * ↑(a - 1)⁻¹ = -1 := by
    norm_cast
    rw [← neg_neg (1 - a), neg_sub, neg_mul, mul_inv_cancel]
    · simp
    · linarith
  rw [this, ← EReal.coe_mul, inv_neg, mul_neg, mul_inv_cancel ha_pos.ne', h_eq]
  simp only [EReal.coe_neg, EReal.coe_one, one_mul]
  congr 4
  norm_cast
  simp only [EReal.coe_sub, EReal.coe_one, sub_sub_cancel_left, EReal.coe_neg, neg_mul, ← h]
  rw_mod_cast [← neg_mul, neg_sub]

lemma renyiDiv_symm (ha_pos : 0 < a) (ha : a < 1)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (1 - a) * renyiDiv a μ ν = a * renyiDiv (1 - a) ν μ :=
  renyiDiv_symm' ha_pos ha (by simp)

-- todo: `ν ≪ μ` is necessary (?) due to the llr being 0 when `(∂μ/∂ν) x = 0`.
-- In that case, `exp (llr μ ν x) = 1 ≠ 0 = (∂μ/∂ν) x`.
lemma coe_cgf_llr_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    [hν : NeZero ν] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hνμ : ν ≪ μ) :
    cgf (llr μ ν) ν a = (a - 1) * renyiDiv a μ ν := by
  rw_mod_cast [renyiDiv_eq_log_integral_of_lt_one ha_pos ha, ← mul_assoc,
    mul_inv_cancel (by linarith), one_mul, cgf, mgf]
  have h_ms : ¬ μ ⟂ₘ ν :=
    fun h ↦ hν.out <| Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hνμ h.symm
  rw [ENNReal.log_ofReal_of_pos]
  swap
  · refine integral_rpow_rnDeriv_pos_iff_not_mutuallySingular ha_pos.ne' ?_ |>.mpr h_ms
    exact integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha
  rw [integral_congr_ae (exp_mul_llr hνμ)]

lemma cgf_llr_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hνμ : ν ≪ μ) :
    cgf (llr μ ν) ν a = (a - 1) * (renyiDiv a μ ν).toReal := by
  by_cases hν : NeZero ν
  swap
  · have ha' : a - 1 < 0 := by linarith
    rw [not_neZero.mp hν]
    by_cases hμ : NeZero μ
    swap; simp [not_neZero.mp hμ, ha', Real.sign_of_neg]
    simp [ha'.ne]
  have : (a - 1) * (renyiDiv a μ ν).toReal = ((a - 1) * renyiDiv a μ ν).toReal := by
    rw [EReal.toReal_mul, ← EReal.coe_one, ← EReal.coe_sub, EReal.toReal_coe]
  rw [this, ← coe_cgf_llr_of_lt_one ha_pos ha hνμ, EReal.toReal_coe]

lemma coe_cgf_llr' (ha_pos : 0 < a) [hν : NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ (1 + a)) ν) (hμν : μ ≪ ν) :
    cgf (llr μ ν) μ a = a * renyiDiv (1 + a) μ ν := by
  rw_mod_cast [renyiDiv_eq_log_integral' (by linarith) (by linarith) h_int hμν, ← mul_assoc,
    add_sub_cancel_left, mul_inv_cancel ha_pos.ne', one_mul, cgf, mgf]
  have h_ms : ¬ μ ⟂ₘ ν :=
    fun h ↦ hν.out <| Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hμν h
  rw [ENNReal.log_ofReal_of_pos _, integral_congr_ae (exp_mul_llr' hμν)]
  simp_rw [← integral_rnDeriv_smul hμν, smul_eq_mul, mul_comm ((∂μ/∂ν) _).toReal,
    ← Real.rpow_add_one' ENNReal.toReal_nonneg (by linarith), add_comm a]
  exact integral_rpow_rnDeriv_pos_iff_not_mutuallySingular (by linarith) h_int |>.mpr h_ms

lemma cgf_llr' (ha_pos : 0 < a) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ (1 + a)) ν) (hμν : μ ≪ ν) :
    cgf (llr μ ν) μ a = a * (renyiDiv (1 + a) μ ν).toReal := by
  by_cases hμ : NeZero μ
  swap
  · rw [not_neZero.mp hμ]
    simp [ha_pos.ne', sign_of_pos ha_pos]
  have : a * (renyiDiv (1 + a) μ ν).toReal = (a * renyiDiv (1 + a) μ ν).toReal := by
    rw [EReal.toReal_mul, EReal.toReal_coe]
  rw [this, ← coe_cgf_llr' ha_pos h_int hμν, EReal.toReal_coe]

section RenyiMeasure
--TODO: change this definition to use the new exp and log instead of the real ones
/-- Density of the Rényi measure `renyiMeasure a μ ν` with respect to `μ + ν`. -/
noncomputable
def renyiDensity (a : ℝ) (μ ν : Measure α) (x : α) : ℝ≥0∞ :=
  ((∂μ/∂(μ + ν)) x) ^ a * ((∂ν/∂(μ + ν)) x) ^ (1 - a)
    * ENNReal.ofReal (exp (- (a - 1) * (renyiDiv a μ ν).toReal))

/-- Tilted measure of `μ` with respect to `ν` parametrized by `a`. -/
noncomputable
def renyiMeasure (a : ℝ) (μ ν : Measure α) : Measure α :=
  (μ + ν).withDensity (renyiDensity a μ ν)

end RenyiMeasure

section Conditional

variable {β γ : Type*} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {κ η : Kernel α β}


/-- Rényi divergence between two kernels κ and η conditional to a measure μ.
It is defined as `Rₐ(κ, η | μ) := Rₐ(μ ⊗ₘ κ, μ ⊗ₘ η)`. -/
noncomputable
def condRenyiDiv (a : ℝ) (κ η : Kernel α β) (μ : Measure α) : EReal :=
  renyiDiv a (μ ⊗ₘ κ) (μ ⊗ₘ η)

/-Maybe this can be stated in a nicer way, but I didn't find a way to do it. It's probably good
enough to use `condRenyiDiv_of_lt_one`.-/
lemma condRenyiDiv_zero (κ η : Kernel α β) (μ : Measure α)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv 0 κ η μ = - ENNReal.log ((μ ⊗ₘ η) {x | 0 < (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x}) := by
  rw [condRenyiDiv, renyiDiv_zero]

@[simp]
lemma condRenyiDiv_one [CountableOrCountablyGenerated α β] (κ η : Kernel α β) (μ : Measure α)
    [IsFiniteKernel κ] [∀ x, NeZero (κ x)] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv 1 κ η μ = condKL κ η μ := by
  rw [condRenyiDiv, renyiDiv_one, kl_compProd_left]

section TopAndBounds

lemma condRenyiDiv_eq_top_iff_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
    (κ η : Kernel α β) (μ : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ = ⊤
      ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
        ∨ ¬Integrable (fun x ↦ ∫ (b : β), ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ
        ∨ ¬ ∀ᵐ x ∂μ, κ x ≪ η x := by
  rw [condRenyiDiv, renyiDiv_eq_top_iff_of_one_lt ha,
    Kernel.Measure.absolutelyContinuous_compProd_right_iff, ← or_assoc]
  refine or_congr_left' fun h_ac ↦ ?_
  rw [integrable_rpow_rnDeriv_compProd_right_iff (by linarith) ha.ne']
  swap;· exact fun _ ↦ not_not.mp h_ac
  tauto

lemma condRenyiDiv_ne_top_iff_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
    (κ η : Kernel α β) (μ : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ ≠ ⊤
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
        ∧ Integrable (fun x ↦ ∫ (b : β), ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ
        ∧ ∀ᵐ x ∂μ, κ x ≪ η x := by
  rw [ne_eq, condRenyiDiv_eq_top_iff_of_one_lt ha]
  push_neg
  rfl

lemma condRenyiDiv_eq_top_iff_of_lt_one [CountableOrCountablyGenerated α β]
    (ha_nonneg : 0 ≤ a) (ha : a < 1)
    (κ η : Kernel α β) (μ : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ = ⊤ ↔ ∀ᵐ a ∂μ, κ a ⟂ₘ η a := by
  rw [condRenyiDiv, renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_nonneg ha,
    Kernel.Measure.mutuallySingular_compProd_iff_of_same_left]

lemma condRenyiDiv_of_not_ae_integrable_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
    (h_int : ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))) :
    condRenyiDiv a κ η μ = ⊤ := by
  rw [condRenyiDiv_eq_top_iff_of_one_lt ha]
  exact Or.inl h_int

lemma condRenyiDiv_of_not_integrable_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
    (h_int : ¬Integrable (fun x ↦ ∫ (b : β), ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condRenyiDiv a κ η μ = ⊤ := by
  rw [condRenyiDiv_eq_top_iff_of_one_lt ha]
  exact Or.inr (Or.inl h_int)

lemma condRenyiDiv_of_not_ac_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] (h_ac : ¬ ∀ᵐ x ∂μ, κ x ≪ η x) :
    condRenyiDiv a κ η μ = ⊤ := by
  rw [condRenyiDiv_eq_top_iff_of_one_lt ha]
  exact Or.inr (Or.inr h_ac)

lemma condRenyiDiv_of_mutuallySingular_of_lt_one [CountableOrCountablyGenerated α β]
    (ha_nonneg : 0 ≤ a) (ha : a < 1) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
    (h_ms : ∀ᵐ x ∂μ, κ x ⟂ₘ η x) :
    condRenyiDiv a κ η μ = ⊤ := by
  rw [condRenyiDiv, renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_nonneg ha]
  exact (Kernel.Measure.mutuallySingular_compProd_iff_of_same_left μ κ η).mpr h_ms

lemma condRenyiDiv_of_ne_zero [CountableOrCountablyGenerated α β] (ha_nonneg : 0 ≤ a)
    (ha_ne_one : a ≠ 1) (κ η : Kernel α β) (μ : Measure α) [IsFiniteKernel κ] [∀ x, NeZero (κ x)]
    [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ = (a - 1)⁻¹
      * ENNReal.log (↑((μ ⊗ₘ η) Set.univ) + (a - 1) * (condHellingerDiv a κ η μ)).toENNReal := by
  rw [condRenyiDiv, renyiDiv_of_ne_one ha_ne_one, hellingerDiv_compProd_left ha_nonneg _]

end TopAndBounds


end Conditional

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β}

lemma le_renyiDiv_of_le_hellingerDiv {a : ℝ} {μ₁ ν₁ : Measure α} {μ₂ ν₂ : Measure β}
    [SigmaFinite μ₁] [SigmaFinite ν₁] [SigmaFinite μ₂] [SigmaFinite ν₂]
    (h_eq : ν₁ Set.univ = ν₂ Set.univ) (h_le : hellingerDiv a μ₁ ν₁ ≤ hellingerDiv a μ₂ ν₂) :
    renyiDiv a μ₁ ν₁ ≤ renyiDiv a μ₂ ν₂ := by
  rcases lt_trichotomy a 1 with (ha | rfl | ha)
  · simp_rw [renyiDiv_of_ne_one ha.ne, h_eq]
    apply EReal.neg_le_neg_iff.mp
    simp_rw [← neg_mul, ← EReal.coe_neg, neg_inv, neg_sub]
    gcongr
    · simp only [EReal.coe_nonneg, inv_nonneg, sub_nonneg, ha.le]
    refine ENNReal.log_monotone <| EReal.toENNReal_le_toENNReal ?_
    gcongr (ν₂ Set.univ) + ?_
    apply EReal.neg_le_neg_iff.mp
    norm_cast
    simp_rw [← neg_mul, ← EReal.coe_neg, neg_sub]
    gcongr
    norm_cast
    linarith
  · simp_all
  · simp_rw [renyiDiv_of_ne_one ha.ne', h_eq]
    gcongr
    · simp only [EReal.coe_nonneg, inv_nonneg, sub_nonneg, ha.le]
    refine ENNReal.log_monotone ?_
    apply EReal.toENNReal_le_toENNReal
    gcongr
    norm_cast
    linarith

lemma le_renyiDiv_compProd [CountableOrCountablyGenerated α β] (ha_pos : 0 < a)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    renyiDiv a μ ν ≤ renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  refine le_renyiDiv_of_le_hellingerDiv ?_ (le_hellingerDiv_compProd ha_pos μ ν κ η)
  rw [Measure.compProd_apply MeasurableSet.univ]
  simp

lemma renyiDiv_fst_le [Nonempty β] [StandardBorelSpace β] (ha_pos : 0 < a)
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ.fst ν.fst ≤ renyiDiv a μ ν :=
  le_renyiDiv_of_le_hellingerDiv Measure.fst_univ (hellingerDiv_fst_le ha_pos μ ν)

lemma renyiDiv_snd_le [Nonempty α] [StandardBorelSpace α] (ha_pos : 0 < a)
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ.snd ν.snd ≤ renyiDiv a μ ν :=
  le_renyiDiv_of_le_hellingerDiv Measure.snd_univ (hellingerDiv_snd_le ha_pos μ ν)

lemma renyiDiv_comp_le_compProd [Nonempty α] [StandardBorelSpace α] (ha_pos : 0 < a)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    renyiDiv a (κ ∘ₘ μ) (η ∘ₘ ν) ≤ renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) :=
  le_renyiDiv_of_le_hellingerDiv (Measure.snd_compProd ν η ▸ Measure.snd_univ)
    (hellingerDiv_comp_le_compProd ha_pos μ ν κ η)

lemma renyiDiv_comp_left_le [Nonempty α] [StandardBorelSpace α]
    (ha_pos : 0 < a) (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    renyiDiv a (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condRenyiDiv a κ η μ :=
  le_renyiDiv_of_le_hellingerDiv (Measure.snd_compProd μ η ▸ Measure.snd_univ)
    (hellingerDiv_comp_le_compProd ha_pos μ μ κ η)

/--The Data Processing Inequality for the Renyi divergence. -/
lemma renyiDiv_comp_right_le [Nonempty α] [StandardBorelSpace α] (ha_pos : 0 < a)
    [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    renyiDiv a (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ renyiDiv a μ ν := by
  refine le_renyiDiv_of_le_hellingerDiv ?_ (hellingerDiv_comp_right_le ha_pos μ ν κ)
  rw [← Measure.snd_compProd ν κ, Measure.snd_univ, Measure.compProd_apply MeasurableSet.univ]
  simp

end DataProcessingInequality

end ProbabilityTheory

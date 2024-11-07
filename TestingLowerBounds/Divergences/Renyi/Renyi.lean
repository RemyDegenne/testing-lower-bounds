/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.Hellinger.Hellinger
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
  filter_upwards [μ.rnDeriv_lt_top ν, Measure.rnDeriv_pos' hνμ] with x hx_lt_top hx_pos
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

noncomputable
abbrev avgMass (a : ℝ) (μ ν : Measure α) : ℝ := (1 - a) * (ν .univ).toReal + a * (μ .univ).toReal

open Classical in
/-- Rényi divergence of order `a`. If `a = 1`, it is defined as `kl μ ν`, otherwise as
`(a - 1)⁻¹ * log (ν(α) + (a - 1) * Hₐ(μ, ν))`.
If `ν` is a probability measure then this becomes the more usual definition
`(a - 1)⁻¹ * log (1 + (a - 1) * Hₐ(μ, ν))`, but this definition maintains some useful properties
also for a general finite measure `ν`, in particular the integral form
`Rₐ(μ, ν) = (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x) ^ a ∂ν)`.
We use ENNReal.log instead of Real.log, because it is monotone on `ℝ≥0∞`, while the real log is
monotone only on `(0, ∞)` (`Real.log 0 = 0`). This allows us to transfer inequalities from the
Hellinger divergence to the Rényi divergence. -/
noncomputable def renyiDiv (a : ℝ) (μ ν : Measure α) : ℝ≥0∞ :=
  if a = 0 then (- ENNReal.log (ν {x | 0 < (∂μ/∂ν) x} / ν .univ)).toENNReal
  else if a = 1 then
    (((μ .univ).toReal⁻¹ : EReal) * (kl μ ν + (μ .univ).toReal - (ν .univ).toReal)
      - log ((μ .univ).toReal / (ν .univ).toReal)).toENNReal
  else ((a - 1)⁻¹ * ENNReal.log
    (((avgMass a μ ν : EReal) + (a - 1) * (hellingerDiv a μ ν)).toENNReal)
      - (a - 1)⁻¹ * Real.log (avgMass a μ ν)).toENNReal

-- log (avgMass a μ ν) = log (μ univ + (1 - a) * (μ univ - ν univ))

-- at 1 from below, (1 - a)⁻¹ * log (avgMass a μ ν) tends to
-- ∞ if μ univ > 1
-- -∞ if μ univ < 1
-- 1 - ν univ if μ univ = 1

lemma avgMass_add_mul_hellingerDiv_nonneg :
    0 ≤ (avgMass a μ ν : EReal) + (a - 1) * (hellingerDiv a μ ν) := by
  sorry

lemma renyi_toENNReal_arg_nonneg (ha_zero : a ≠ 0) (ha_ne_one : a ≠ 1) :
    0 ≤ (a - 1)⁻¹ * ENNReal.log
      (((avgMass a μ ν : EReal) + (a - 1) * (hellingerDiv a μ ν)).toENNReal)
      - (a - 1)⁻¹ * Real.log (avgMass a μ ν) := by
  rcases lt_trichotomy a 1 with ha | rfl | ha
  swap; · simp
  · -- a < 1
    rw [EReal.sub_nonneg]
    rotate_left
    · norm_cast; exact EReal.coe_ne_top _
    · norm_cast; exact EReal.coe_ne_bot _
    sorry
  · -- 1 < a
    sorry

open Classical in
@[simp]
lemma renyiDiv_zero (μ ν : Measure α) :
    renyiDiv 0 μ ν = (- ENNReal.log (ν {x | 0 < (∂μ/∂ν) x} / ν .univ)).toENNReal :=
  if_pos rfl

@[simp]
lemma renyiDiv_one (μ ν : Measure α) :
    renyiDiv 1 μ ν
      = (((μ .univ).toReal⁻¹ : EReal) * (kl μ ν + (μ .univ).toReal - (ν .univ).toReal)
        - log ((μ .univ).toReal / (ν .univ).toReal)).toENNReal := by
  rw [renyiDiv, if_neg one_ne_zero, if_pos rfl]

lemma renyiDiv_of_ne_one (ha_zero : a ≠ 0) (ha_ne_one : a ≠ 1) (μ ν : Measure α) :
    renyiDiv a μ ν = ((a - 1)⁻¹ * ENNReal.log
      (((avgMass a μ ν : EReal) + (a - 1) * (hellingerDiv a μ ν)).toENNReal)
      - (a - 1)⁻¹ * Real.log (avgMass a μ ν)).toENNReal := by
  rw [renyiDiv, if_neg ha_zero, if_neg ha_ne_one]

open Classical in
lemma renyiDiv_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ha_pos : 0 < a) (ha_lt : a < 1) :
    renyiDiv a μ ν =
      if μ ⟂ₘ ν then ∞
      else ENNReal.ofReal ((a - 1)⁻¹
        * (Real.log (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν) - Real.log (avgMass a μ ν))) := by
  rw [renyiDiv_of_ne_one ha_pos.ne' ha_lt.ne]
  rw [← hellingerDiv_eq_add_measure_univ_iff_of_lt_one ha_pos ha_lt]
  split_ifs with h
  · suffices (avgMass a μ ν : EReal) + (a - 1) * (hellingerDiv a μ ν) = 0 by
      rw [this]
      simp only [ne_eq, EReal.zero_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
        EReal.toReal_zero, ENNReal.ofReal_zero, ENNReal.log_zero, EReal.toENNReal_eq_top_iff]
      have : (((a - 1)⁻¹ : ℝ) : EReal) * ⊥ = ⊤ := by
        sorry
      rw [this, sub_eq_add_neg, EReal.top_add_of_ne_bot]
      simp only [ne_eq, EReal.neg_eq_bot_iff]
      norm_cast
      exact EReal.coe_ne_top _
    rw [h]
    simp only [EReal.coe_add, EReal.coe_mul, EReal.coe_sub, EReal.coe_one, ne_eq, measure_ne_top,
      not_false_eq_true, EReal.coe_ennreal_add,
      EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal]
    rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _),
      ← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
    norm_cast
    have : max (a * (1 - a)⁻¹) 0 = a * (1 - a)⁻¹ := by
      sorry
    rw [this, ← neg_sub 1 a, mul_add, ← mul_assoc, ← mul_assoc, mul_comm _ a, neg_mul, mul_assoc a,
      neg_mul, mul_inv_cancel₀]
    · ring
    · exact sub_ne_zero.mpr ha_lt.ne'
  · rw [← mul_hellingerDiv_add_meas_eq_integral_of_lt_one ha_pos ha_lt]
    sorry

lemma renyiDiv_of_one_lt (ha_lt : 1 < a) :
    renyiDiv a μ ν =
      if hellingerDiv a μ ν = ∞ then ∞
      else ENNReal.ofReal ((a - 1)⁻¹
        * (Real.log (∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν) - Real.log (avgMass a μ ν))) := by
  sorry

@[simp]
lemma renyiDiv_zero_measure_left (ha_nonneg : 0 ≤ a) (ν : Measure α) [IsFiniteMeasure ν] :
    renyiDiv a 0 ν = if a < 1 then ∞ else 0 := by
  by_cases ha_zero : a = 0
  · simp only [ha_zero, renyiDiv_zero, zero_lt_one, ↓reduceIte, EReal.toENNReal_eq_top_iff,
      EReal.neg_eq_top_iff, ENNReal.log_eq_bot_iff, ENNReal.div_eq_zero_iff, measure_ne_top, or_false]
    sorry
  by_cases ha : a = 1
  · simp [ha]
  rw [renyiDiv_of_ne_one ha_zero ha]
  simp only [EReal.coe_add, EReal.coe_mul, EReal.coe_sub, EReal.coe_one, ne_eq, measure_ne_top,
    not_false_eq_true, ENNReal.toReal_toEReal_of_ne_top, Measure.coe_zero, Pi.zero_apply,
    ENNReal.zero_toReal, mul_zero, EReal.coe_zero, add_zero,
    hellingerDiv_zero_measure_left (ha_nonneg.lt_of_ne' ha_zero)]
  have : (1 - (a : EReal)) * (ν Set.univ) + (a - 1) * (ν Set.univ) = 0 := by
    rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
    norm_cast
    ring
  simp only [this, ne_eq, EReal.zero_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
    EReal.toReal_zero, ENNReal.ofReal_zero, ENNReal.log_zero]
  rcases lt_or_le a 1 with ha_lt | ha_lt
  · simp only [ha_lt, ↓reduceIte, EReal.toENNReal_eq_top_iff]
    have : (((a - 1)⁻¹ : ℝ) : EReal) * ⊥ = ⊤ := by
      sorry
    rw [this, sub_eq_add_neg, EReal.top_add_of_ne_bot]
    simp only [ne_eq, EReal.neg_eq_bot_iff]
    norm_cast
    exact EReal.coe_ne_top _
  · have : (((a - 1)⁻¹ : ℝ) : EReal) * ⊥ = ⊥ := by
      sorry
    simp [this, not_lt.mpr ha_lt]

@[simp]
lemma renyiDiv_zero_measure_right (ha_nonneg : 0 ≤ a)
    (μ : Measure α) [IsFiniteMeasure μ] [NeZero μ] :
    renyiDiv a μ 0 = ∞ := by
  by_cases ha_zero : a = 0
  · simp [ha_zero]
  have ha_pos : 0 < a := ha_nonneg.lt_of_ne' ha_zero
  rcases lt_trichotomy a 1 with (ha | rfl | ha)
  · rw [renyiDiv_of_ne_one ha_zero ha.ne, hellingerDiv_zero_measure_right_of_lt_one ha_pos ha]
    simp only [EReal.coe_add, Measure.coe_zero, Pi.zero_apply, ENNReal.zero_toReal, mul_zero,
      EReal.coe_zero, EReal.coe_mul, zero_add, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal,
      EReal.toENNReal_eq_top_iff]
    have : (a : EReal) * (μ Set.univ).toReal + (a - 1) * ((max (a * (1 - a)⁻¹) 0) * (μ Set.univ))
        = 0 := by
      sorry
    simp only [this, ne_eq, EReal.zero_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
      EReal.toReal_zero, ENNReal.ofReal_zero, ENNReal.log_zero]
    simp only [EReal.coe_neg', inv_neg'', sub_neg.mpr ha, EReal.mul_bot_of_neg]
    rw [sub_eq_add_neg, EReal.top_add_of_ne_bot]
    simp only [ne_eq, EReal.neg_eq_bot_iff]
    norm_cast
    exact EReal.coe_ne_top _
  · simp only [renyiDiv_one, kl_zero_right, EReal.coe_ennreal_top, ne_eq, EReal.coe_ne_bot,
      not_false_eq_true, EReal.top_add_of_ne_bot, Measure.coe_zero, Pi.zero_apply,
      ENNReal.zero_toReal, EReal.coe_zero, sub_zero, div_zero, log_zero, EReal.toENNReal_eq_top_iff]
    rw [EReal.mul_eq_top]
    simp only [not_top_lt, and_false, top_ne_bot, EReal.zero_lt_top, and_true, false_or]
    right
    rw [← EReal.coe_inv]
    norm_cast
    rw [inv_pos, ENNReal.toReal_pos_iff]
    simp [NeZero.ne μ]
  · rw [renyiDiv_of_ne_one ha_zero ha.ne', hellingerDiv_zero_measure_right_of_one_le ha.le]
    simp only [EReal.coe_add, Measure.coe_zero, Pi.zero_apply, ENNReal.zero_toReal, mul_zero,
      EReal.coe_zero, EReal.coe_mul, zero_add, EReal.coe_ennreal_top, EReal.toENNReal_eq_top_iff]
    have : ((a : EReal) - 1) * ⊤ = ⊤ := by
      sorry
    rw [this, EReal.add_top_of_ne_bot]
    swap; · sorry
    simp only [EReal.toENNReal_top, ENNReal.log_top]
    have : (((a - 1)⁻¹ : ℝ) : EReal) * ⊤ = ⊤ := by
      sorry
    rw [this, sub_eq_add_neg, EReal.top_add_of_ne_bot]
    simp only [ne_eq, EReal.neg_eq_bot_iff]
    norm_cast
    exact EReal.coe_ne_top _

section RenyiEq

lemma renyiDiv_eq_top_of_hellingerDiv_eq_top [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : hellingerDiv a μ ν = ∞) :
    renyiDiv a μ ν = ∞ := by
  by_cases ha_one : a = 1
  · rw [ha_one, hellingerDiv_one] at h
    rw [ha_one, renyiDiv_one, h]
    simp only [ne_eq, measure_ne_top, not_false_eq_true, ENNReal.toReal_toEReal_of_ne_top,
      EReal.coe_ennreal_top, EReal.coe_ennreal_ne_bot, EReal.top_add_of_ne_bot, sub_eq_add_neg,
      EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff, EReal.toENNReal_eq_top_iff]
    rw [(EReal.mul_eq_top _ _).mpr, EReal.top_add_of_ne_bot]
    · simp
    · simp only [not_top_lt, and_false, top_ne_bot, EReal.zero_lt_top, and_true, false_or]
      rw [← ENNReal.toReal_toEReal_of_ne_top (measure_ne_top _ _)]
      rw [← EReal.coe_inv]
      norm_cast
      rw [inv_pos, ENNReal.toReal_pos_iff]
      simp [NeZero.ne μ]
  have ha : 1 < a := by
    by_contra ha
    exact hellingerDiv_ne_top_of_lt_one (lt_of_le_of_ne (not_lt.mp ha) ha_one) _ _ h
  rw [renyiDiv_of_one_lt ha, if_pos h]

lemma renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_lt
    [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha : 1 < a) :
    renyiDiv a μ ν = ∞ ↔ hellingerDiv a μ ν = ∞ := by
  refine ⟨fun h ↦ ?_, fun h ↦ renyiDiv_eq_top_of_hellingerDiv_eq_top h⟩
  contrapose! h
  rw [renyiDiv_of_one_lt ha]
  simp [h]

lemma renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le (ha : 1 ≤ a)
    [SigmaFinite μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ∞ ↔ hellingerDiv a μ ν = ∞ := by
  by_cases ha_one : a = 1
  · rw [ha_one, renyiDiv_one, hellingerDiv_one]
  · exact renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_lt
      (lt_of_le_of_ne ha fun h ↦ ha_one h.symm)

lemma renyiDiv_eq_top_iff_of_one_lt (ha : 1 < a) [SigmaFinite μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ∞ ↔ ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∨ ¬ μ ≪ ν := by
  simp_rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le ha.le,
    ← integrable_hellingerFun_iff_integrable_rpow ha.ne', hellingerDiv_eq_top_iff, ha.le, true_and]

lemma renyiDiv_ne_top_iff_of_one_lt (ha : 1 < a) [SigmaFinite μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν ≠ ∞ ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∧ μ ≪ ν := by
  rw [ne_eq, renyiDiv_eq_top_iff_of_one_lt ha]
  simp

lemma renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ∞ ↔ μ ⟂ₘ ν := by
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
    renyiDiv a μ ν = ∞ := by
  by_cases ha : a < 1
  · rw [renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_nonneg ha]
    exact hμν
  · rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le (le_of_not_lt ha)]
    exact hellingerDiv_of_mutuallySingular_of_one_le (le_of_not_lt ha) hμν

lemma renyiDiv_of_one_lt_of_not_integrable (ha : 1 < a) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_int : ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) :
    renyiDiv a μ ν = ∞ := by
  rw [renyiDiv_eq_top_iff_of_one_lt ha]
  exact Or.inl h_int

lemma renyiDiv_of_one_le_of_not_ac (ha : 1 ≤ a) (h_ac : ¬ μ ≪ ν)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ∞ := by
  by_cases ha_one : a = 1
  · rw [ha_one, renyiDiv_one]
    exact kl_of_not_ac h_ac
  replace ha : 1 < a := lt_of_le_of_ne ha fun h ↦ ha_one h.symm
  rw [renyiDiv_eq_top_iff_of_one_lt ha]
  exact Or.inr h_ac

end RenyiEq

lemma forall_renyiDiv_eq_top_of_eq_top_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) [NeZero μ]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : renyiDiv a μ ν = ∞) :
    ∀ a', 0 ≤ a' → renyiDiv a' μ ν = ∞ := by
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

lemma renyiDiv_symm' (ha_pos : 0 < a) (ha : a < 1) (h_eq : μ .univ = ν .univ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (1 - a) * renyiDiv a μ ν = a * renyiDiv (1 - a) ν μ := by
  rw [renyiDiv_of_ne_one ha.ne, renyiDiv_of_ne_one (by linarith)]
  simp only [sub_sub_cancel_left, neg_mul]
  rw [← mul_assoc, ← mul_assoc]
  have h : (1 - a) * hellingerDiv a μ ν = a * hellingerDiv (1 - a) ν μ :=
    hellingerDiv_symm' ha_pos ha h_eq
  have : (1 - (a : EReal)) * ↑(a - 1)⁻¹ = -1 := by
    norm_cast
    rw [← neg_neg (1 - a), neg_sub, neg_mul, mul_inv_cancel₀]
    · simp
    · linarith
  rw [this, ← EReal.coe_mul, inv_neg, mul_neg, mul_inv_cancel₀ ha_pos.ne', h_eq]
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
    mul_inv_cancel₀ (by linarith), one_mul, cgf, mgf]
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
    add_sub_cancel_left, mul_inv_cancel₀ ha_pos.ne', one_mul, cgf, mgf]
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

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β}

lemma le_renyiDiv_of_le_hellingerDiv {a : ℝ} {μ₁ ν₁ : Measure α} {μ₂ ν₂ : Measure β}
    [SigmaFinite μ₁] [SigmaFinite ν₁] [SigmaFinite μ₂] [SigmaFinite ν₂]
    (h_eq : ν₁ .univ = ν₂ .univ) (h_le : hellingerDiv a μ₁ ν₁ ≤ hellingerDiv a μ₂ ν₂) :
    renyiDiv a μ₁ ν₁ ≤ renyiDiv a μ₂ ν₂ := by
  rcases lt_trichotomy a 1 with (ha | rfl | ha)
  · simp_rw [renyiDiv_of_ne_one ha.ne, h_eq]
    apply EReal.neg_le_neg_iff.mp
    simp_rw [← neg_mul, ← EReal.coe_neg, neg_inv, neg_sub]
    gcongr
    · simp only [EReal.coe_nonneg, inv_nonneg, sub_nonneg, ha.le]
    refine ENNReal.log_monotone <| EReal.toENNReal_le_toENNReal ?_
    gcongr (ν₂ .univ) + ?_
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
    refine ENNReal.log_monotone <| EReal.toENNReal_le_toENNReal ?_
    gcongr
    norm_cast
    linarith

lemma le_renyiDiv_compProd [CountableOrCountablyGenerated α β] (ha_pos : 0 < a)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    renyiDiv a μ ν ≤ renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) :=
  le_renyiDiv_of_le_hellingerDiv Measure.compProd_apply_univ.symm
    (le_hellingerDiv_compProd ha_pos μ ν κ η)

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

/--The Data Processing Inequality for the Renyi divergence. -/
lemma renyiDiv_comp_right_le [Nonempty α] [StandardBorelSpace α] (ha_pos : 0 < a)
    [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    renyiDiv a (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ renyiDiv a μ ν :=
  le_renyiDiv_of_le_hellingerDiv Measure.comp_apply_univ (hellingerDiv_comp_right_le ha_pos μ ν κ)

end DataProcessingInequality

end ProbabilityTheory

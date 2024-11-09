/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Divergences.Chernoff
import TestingLowerBounds.Testing.ChangeMeasure

/-!

# Change of measure inequalities involving Rényi divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open MeasureTheory Real

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν ν' : Measure α} {s : Set α}

lemma measure_llr_gt_renyiDiv_le_exp [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a : ℝ} (ha : 0 < a) (c : ℝ) (h : renyiDiv (1 + a) μ ν ≠ ∞) :
    (μ {x | (renyiDiv (1 + a) μ ν).toReal + c < llr μ ν x}).toReal ≤ exp (-a * c) := by
  have hμν : μ ≪ ν := by
    by_contra h_not
    exact h (renyiDiv_of_one_le_of_not_ac (by linarith) h_not)
  rw [renyiDiv_ne_top_iff_of_one_lt (by linarith)] at h
  calc (μ {x | (renyiDiv (1 + a) μ ν).toReal + c < llr μ ν x}).toReal
  _ ≤ (μ {x | (renyiDiv (1 + a) μ ν).toReal + c ≤ llr μ ν x}).toReal := by
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun x ↦ ?_))
        simp only [Set.mem_setOf_eq]
        exact le_of_lt
  _ ≤ exp (-a * ((renyiDiv (1 + a) μ ν).toReal + c) + cgf (llr μ ν) μ a) := by
        refine measure_ge_le_exp_cgf (X := llr μ ν) (μ := μ) ((renyiDiv (1 + a) μ ν).toReal + c)
          ha.le ?_
        rw [integrable_congr (exp_mul_llr' hμν)]
        · rw [integrable_rpow_rnDeriv_iff hμν ha]
          exact h.1
  _ = exp (-a * c) := by
        congr
        sorry
        -- rw [cgf_llr' ha h.1 h.2]
        --ring

lemma measure_sub_le_measure_mul_exp_renyiDiv [NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : Set α) {a : ℝ} (ha : 0 < a) (c : ℝ) (h : renyiDiv (1 + a) μ ν ≠ ∞) :
    (μ s).toReal - exp (- a * c) ≤ (ν s).toReal * exp ((renyiDiv (1 + a) μ ν).toReal + c) := by
  have hμν : μ ≪ ν := by
    by_contra h_not
    exact h (renyiDiv_of_one_le_of_not_ac (by linarith) h_not)
  refine le_trans ?_ (measure_sub_le_measure_mul_exp hμν s ((renyiDiv (1 + a) μ ν).toReal + c)
    (measure_ne_top _ _))
  gcongr
  exact measure_llr_gt_renyiDiv_le_exp ha c h

lemma one_sub_exp_le_add_measure_mul_exp_max_renyiDiv [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure ν'] (s : Set α)
    {a : ℝ} (ha : 0 < a) (c : ℝ)
    (hν : renyiDiv (1 + a) μ ν ≠ ⊤) (hν' : renyiDiv (1 + a) μ ν' ≠ ∞) :
    1 - 2 * exp (- a * c)
      ≤ ((ν s).toReal + (ν' sᶜ).toReal)
        * exp (max (renyiDiv (1 + a) μ ν).toReal (renyiDiv (1 + a) μ ν').toReal + c) := by
  have hμν : μ ≪ ν := by
    by_contra h_not
    exact hν (renyiDiv_of_one_le_of_not_ac (by linarith) h_not)
  have hμν' : μ ≪ ν' := by
    by_contra h_not
    exact hν' (renyiDiv_of_one_le_of_not_ac (by linarith) h_not)
  calc 1 - 2 * exp (- a * c)
  _ = 1 - exp (- a * c) - exp (- a * c) := by ring
  _ ≤ 1 - (μ {x | (renyiDiv (1 + a) μ ν).toReal + c < llr μ ν x}).toReal
      - (μ {x | (renyiDiv (1 + a) μ ν').toReal + c < llr μ ν' x}).toReal := by
        gcongr
        · exact measure_llr_gt_renyiDiv_le_exp ha c hν
        · exact measure_llr_gt_renyiDiv_le_exp ha c hν'
  _ ≤ ((ν s).toReal + (ν' sᶜ).toReal)
      * exp (max ((renyiDiv (1 + a) μ ν).toReal + c) ((renyiDiv (1 + a) μ ν').toReal + c)) :=
        one_sub_le_add_measure_mul_exp' hμν hμν' s _ _
  _ = ((ν s).toReal + (ν' sᶜ).toReal)
        * exp (max (renyiDiv (1 + a) μ ν).toReal (renyiDiv (1 + a) μ ν').toReal + c) := by
        rw [max_add_add_right]

lemma exp_neg_max_renyiDiv_le_add_measure [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure ν'] (s : Set α)
    {a : ℝ} (ha : 0 < a) (hν : renyiDiv (1 + a) μ ν ≠ ∞) (hν' : renyiDiv (1 + a) μ ν' ≠ ∞) :
    2⁻¹ * exp (- max (renyiDiv (1 + a) μ ν).toReal (renyiDiv (1 + a) μ ν').toReal - log 4 / a)
      ≤ (ν s).toReal + (ν' sᶜ).toReal := by
  have h := one_sub_exp_le_add_measure_mul_exp_max_renyiDiv s ha (log 4 / a) hν hν'
  have : 1 - 2 * exp (-a * (log 4 / a)) = 2⁻¹ := by
    rw [neg_mul, mul_div_cancel₀ _ ha.ne', exp_neg, exp_log]
    · norm_num
    · positivity
  rw [this] at h
  rwa [neg_sub_left, exp_neg, mul_inv_le_iff₀ (exp_pos _), add_comm (log 4 / a)]

end ProbabilityTheory

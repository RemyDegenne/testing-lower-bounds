/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Renyi
import TestingLowerBounds.Testing.ChangeMeasure
import Mathlib.Probability.Moments

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

lemma measure_llr_gt_renyiDiv_le_exp [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    {a : ℝ} (ha : 0 < a) (c : ℝ) (h : renyiDiv (1 + a) μ ν ≠ ⊤) :
    (μ {x | EReal.toReal (renyiDiv (1 + a) μ ν) + c < llr μ ν x}).toReal ≤ exp (-a * c) := by
  calc (μ {x | EReal.toReal (renyiDiv (1 + a) μ ν) + c < llr μ ν x}).toReal
  _ ≤ (μ {x | EReal.toReal (renyiDiv (1 + a) μ ν) + c ≤ llr μ ν x}).toReal := by
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun x ↦ ?_))
        simp only [Set.mem_setOf_eq]
        exact le_of_lt
  _ ≤ exp (-a * ((renyiDiv (1 + a) μ ν).toReal + c) + cgf (llr μ ν) μ a) := by
        refine measure_ge_le_exp_cgf (X := llr μ ν) (μ := μ) ((renyiDiv (1 + a) μ ν).toReal + c)
          ha.le ?_
        sorry
  _ = exp (-a * c) := by
        congr
        rw [cgf_llr' ha h]
        ring

lemma measure_sub_le_measure_mul_exp_renyiDiv [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (s : Set α) {a : ℝ} (ha : 0 < a) (c : ℝ) (h : renyiDiv (1 + a) μ ν ≠ ⊤) :
    (μ s).toReal - exp (- a * c) ≤ (ν s).toReal * exp ((renyiDiv (1 + a) μ ν).toReal + c) := by
  refine le_trans ?_ (measure_sub_le_measure_mul_exp hμν s ((renyiDiv (1 + a) μ ν).toReal + c)
    (measure_ne_top _ _))
  gcongr
  exact measure_llr_gt_renyiDiv_le_exp ha c h

lemma one_sub_exp_le_add_measure_mul_exp_max_renyiDiv [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] (hμν : μ ≪ ν) (hμν' : μ ≪ ν') (s : Set α)
    {a : ℝ} (ha : 0 < a) (c : ℝ)
    (hν : renyiDiv (1 + a) μ ν ≠ ⊤) (hν' : renyiDiv (1 + a) μ ν' ≠ ⊤) :
    1 - 2 * exp (- a * c)
      ≤ ((ν s).toReal + (ν' sᶜ).toReal)
        * exp (max (renyiDiv (1 + a) μ ν).toReal (renyiDiv (1 + a) μ ν').toReal + c) := by
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

end ProbabilityTheory

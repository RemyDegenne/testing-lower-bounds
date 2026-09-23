/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Divergences.Renyi.Renyi

/-!
# Chernoff divergence

## Main definitions

* `chernoffDiv a μ ν`: the Chernoff divergence, `⨅ ξ, max (klDiv ξ μ) (klDiv ξ ν)` over
  probability measures `ξ`.

## Main statements

* `chernoffDiv_one`: the Chernoff divergence of order `1` as an infimum of Kullback-Leibler
  divergences.

-/

open Real MeasureTheory InformationTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

/-- Chernoff divergence of order `a` between two measures `μ, ν`.
This is the infimum over probability measures `ξ` of the maximum of the Rényi divergences
of order `a` from `ξ` to `μ` and from `ξ` to `ν`. -/
noncomputable def chernoffDiv (a : ℝ) (μ ν : Measure α) : ℝ≥0∞ :=
  ⨅ (ξ : Measure α) (_hξ : IsProbabilityMeasure ξ), max (renyiDiv a ξ μ) (renyiDiv a ξ ν)

lemma chernoffDiv_one [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    chernoffDiv 1 μ ν
      = ⨅ (ξ : Measure α) (_hξ : IsProbabilityMeasure ξ), max (klDiv ξ μ) (klDiv ξ ν) := by
  simp_rw [chernoffDiv, renyiDiv_one]
  congr with ξ
  congr with hξ
  simp only [measure_univ, ENNReal.toReal_one, EReal.coe_one, inv_one, one_mul, ne_eq, one_ne_zero,
    not_false_eq_true, div_self, log_one, EReal.coe_zero, sub_zero]
  have : (1 : EReal) = ((1 : ℝ) : EReal) := rfl
  simp_rw [this, EReal.add_sub_cancel_right]
  simp

end ProbabilityTheory

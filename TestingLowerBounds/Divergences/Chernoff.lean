/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Divergences.Renyi

/-!
# Chernoff divergence

## Main definitions

* `chernoffDiv`

## Main statements

* `fooBar_unique`

-/

open Real MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

/-- Chernoff divergence of order `a` between two measures `μ, ν`.
This is the infimum over probability measures `ξ` of the maximum of the Rényi divergences
of order `a` from `ξ` to `μ` and from `ξ` to `ν`. -/
noncomputable def chernoffDiv (a : ℝ) (μ ν : Measure α) : EReal :=
  ⨅ (ξ : Measure α) (_hξ : IsProbabilityMeasure ξ), max (renyiDiv a ξ μ) (renyiDiv a ξ ν)

lemma chernoffDiv_one (μ ν : Measure α) :
    chernoffDiv 1 μ ν
      = ⨅ (ξ : Measure α) (_hξ : IsProbabilityMeasure ξ), max (kl ξ μ) (kl ξ ν) := by
  simp_rw [chernoffDiv, renyiDiv_one]

end ProbabilityTheory

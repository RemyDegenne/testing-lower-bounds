/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Divergences.StatInfo.StatInfo
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# DeGroot statistical information

## Main definitions

* `deGrootInfo`

## Main statements

* `deGrootInfo_comp_le`

## Notation

## Implementation details

-/

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞}

/-- The DeGroot statistical information between two measures, for prior Bernoulli `p`. -/
noncomputable
def deGrootInfo (μ ν : Measure 𝒳) (p : ℝ≥0∞) (hp : p ≤ 1) : ℝ≥0∞ :=
  statInfo μ ν (PMF.bernoulli p.toNNReal (by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top hp),
      ENNReal.coe_one]
    exact hp)).toMeasure

/-- **Data processing inequality** for the DeGroot statistical information. -/
lemma deGrootInfo_comp_le (μ ν : Measure 𝒳) (p : ℝ≥0∞) (hp : p ≤ 1)
    (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] :
    deGrootInfo (η ∘ₘ μ) (η ∘ₘ ν) p hp ≤ deGrootInfo μ ν p hp := statInfo_comp_le _ _ _ _

end ProbabilityTheory

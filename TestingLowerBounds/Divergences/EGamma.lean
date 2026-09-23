/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import TestingLowerBounds.Divergences.StatInfo.StatInfo

/-!
# E_gamma / hockey-stick divergence

## Main definitions

* `deGrootInfo`

## Main statements

* `deGrootInfo_comp_le`

## Notation

## Implementation details

-/

@[expose] public section

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞}

/-- The hockey-stick divergence. -/
noncomputable
def eGamma (μ ν : Measure 𝒳) (γ : ℝ≥0∞) : ℝ≥0∞ :=
  statInfo μ ν (Measure.dirac false + γ • Measure.dirac true)

/-- **Data processing inequality** for the hockey-stick divergence. -/
lemma eGamma_comp_le (μ ν : Measure 𝒳) (γ : ℝ≥0∞) (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] :
    eGamma (η ∘ₘ μ) (η ∘ₘ ν) γ ≤ eGamma μ ν γ := statInfo_comp_le _ _ _ _

end ProbabilityTheory

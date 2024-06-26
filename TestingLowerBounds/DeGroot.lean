/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Testing.Binary

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

noncomputable
def statInfo (μ ν : Measure 𝒳) (π : Measure Bool) : ℝ≥0∞ :=
  min (π {false} * μ Set.univ) (π {true} * μ Set.univ) - bayesBinaryRisk' μ ν π

/-- **Data processing inequality** for the statistical information. -/
lemma statInfo_comp_le (μ ν : Measure 𝒳) (π : Measure Bool) (η : kernel 𝒳 𝒳') [IsMarkovKernel η] :
    statInfo (μ ∘ₘ η) (ν ∘ₘ η) π ≤ statInfo μ ν π := by
  refine tsub_le_tsub ?_ (bayesBinaryRisk'_le_bayesBinaryRisk'_comp _ _ _ _)
  rw [Measure.bind_apply MeasurableSet.univ (kernel.measurable _)]
  simp

/-- The DeGroot statistical information between two measures, for prior Bernoulli `p`. -/
noncomputable
def deGrootInfo (μ ν : Measure 𝒳) (p : ℝ≥0∞) (hp : p ≤ 1) : ℝ≥0∞ :=
  min p (1 - p) - bayesBinaryRisk μ ν p hp

/-- **Data processing inequality** for the DeGroot statistical information. -/
lemma deGrootInfo_comp_le (μ ν : Measure 𝒳) (p : ℝ≥0∞) (hp : p ≤ 1)
    (η : kernel 𝒳 𝒳') [IsMarkovKernel η] :
    deGrootInfo (μ ∘ₘ η) (ν ∘ₘ η) p hp ≤ deGrootInfo μ ν p hp :=
  tsub_le_tsub le_rfl (bayesBinaryRisk_le_bayesBinaryRisk_comp _ _ _ _)

end ProbabilityTheory

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.Order.CompletePartialOrder
import TestingLowerBounds.CurvatureMeasure
import TestingLowerBounds.Divergences.StatInfo
import TestingLowerBounds.FDiv.Measurable

/-!
# Integrals of statistical informations

-/

open MeasureTheory Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞} {π : Measure Bool} {f : ℝ → ℝ} {β γ x t : ℝ}

section Definition

noncomputable
def expectedInfo (γ : Measure (Measure Bool)) (μ ν : Measure 𝒳) : ℝ≥0∞ :=
  ∫⁻ π, statInfo μ ν π ∂γ


end Definition

end ProbabilityTheory

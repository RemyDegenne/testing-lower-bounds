/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.ForMathlib.RnDeriv

/-!

# Bayes risk of a test with two simple hypotheses

## Main definitions

*

## Main statements

*

# TODO

* Define the Bayes risk more generally, with losses etc.

-/

open scoped ENNReal

open MeasureTheory

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α}

noncomputable
def todo (μ ν : Measure α) (p : ℝ≥0∞) (φ : α → ℝ≥0∞) : ℝ≥0∞ :=
  p * ∫⁻ x, φ x ∂μ + (1 - p) * ∫⁻ x, 1 - φ x ∂ν

noncomputable
def bayesRiskTwo (μ ν : Measure α) (p : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (φ) (_ : ∀ x, φ x ≤ 1), todo μ ν p φ

end ProbabilityTheory

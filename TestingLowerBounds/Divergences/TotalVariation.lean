/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Testing.BoolMeasure
import TestingLowerBounds.Divergences.StatInfo.StatInfo

/-!
# Total variation distance

## Main definitions

* `tv μ ν`: the total variation distance between `μ` and `ν`, defined as the statistical
  information `statInfo μ ν π` for the uniform prior `π` on `Bool`.

## Main statements

* `tv_le`: `tv μ ν ≤ min (μ univ) (ν univ)`.
* `tv_comp_le`: data-processing inequality.

-/

open MeasureTheory Bool

open scoped ENNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳}

/-- Total variation distance between two measures. -/
noncomputable def tv (μ ν : Measure 𝒳) : ℝ :=
  (statInfo μ ν (boolMeasure 1 1)).toReal

instance : IsFiniteMeasure (boolMeasure 1 1) := by constructor; simp

@[simp] lemma tv_zero_left : tv (0 : Measure 𝒳) ν = 0 := by simp [tv]

@[simp] lemma tv_zero_right : tv μ (0 : Measure 𝒳) = 0 := by simp [tv]

@[simp] lemma tv_self : tv μ μ = 0 := by simp [tv]

lemma tv_nonneg : 0 ≤ tv μ ν := ENNReal.toReal_nonneg

lemma tv_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tv μ ν ≤ min (μ .univ).toReal (ν .univ).toReal := by
  rw [← ENNReal.toReal_min (measure_ne_top _ _) (measure_ne_top _ _)]
  refine ENNReal.toReal_mono ?_ ?_
  · simp
  · have h := statInfo_le_min (μ := μ) (ν := ν) (π := boolMeasure 1 1)
    simpa only [boolMeasure_apply_false, one_mul, boolMeasure_apply_true] using h

/-- **Data processing inequality** for the total variation. -/
lemma tv_comp_le (μ ν : Measure 𝒳) [IsFiniteMeasure μ] (κ : Kernel 𝒳 𝒳') [IsMarkovKernel κ] :
    tv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tv μ ν := by
  exact ENNReal.toReal_mono statInfo_ne_top (statInfo_comp_le _ _ _ _)

end ProbabilityTheory

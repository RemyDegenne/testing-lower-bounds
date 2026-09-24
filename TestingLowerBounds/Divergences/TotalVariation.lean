/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import TestingLowerBounds.Testing.BoolMeasure
public import TestingLowerBounds.Divergences.StatInfo.StatInfo

/-!
# Total variation distance

## Main definitions

* `tv μ ν`: the total variation distance between `μ` and `ν`, defined as the statistical
  information `statInfo μ ν π` for the uniform prior `π` on `Bool`.

## Main statements

* `tv_le`: `tv μ ν ≤ min (μ univ) (ν univ)`.
* `lintegral_one_sub_rnDeriv_eq_tv`: `∫⁻ x, 1 - (∂μ/∂ν) x ∂ν = tv μ ν` for probability measures.
* `tv_comp_le`: data-processing inequality.

-/

@[expose] public section

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

lemma tv_symm (μ ν : Measure 𝒳) : tv μ ν = tv ν μ := by
  rw [tv, tv, statInfo_symm]
  congr 2
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton b)]
  cases b <;> simp [Set.preimage]

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

lemma lintegral_one_sub_rnDeriv_eq_tv (μ ν : Measure 𝒳) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ∫⁻ x, 1 - (∂μ/∂ν) x ∂ν = ENNReal.ofReal (tv μ ν) := by
  have h := toReal_statInfo_eq_integral_max_of_ge (μ := μ) (ν := ν) (π := Bool.boolMeasure 1 1)
    (by simp)
  simp only [Bool.boolMeasure_apply_true, Bool.boolMeasure_apply_false, ENNReal.toReal_one,
    one_mul] at h
  rw [tv, h, ofReal_integral_eq_lintegral_ofReal]
  · refine lintegral_congr_ae ?_
    filter_upwards [μ.rnDeriv_ne_top ν] with x hx
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, zero_max,
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_toReal hx]
  · exact (integrable_zero _ _ _).sup ((integrable_const _).sub Measure.integrable_toReal_rnDeriv)
  · exact ae_of_all _ fun _ ↦ le_max_left _ _

end ProbabilityTheory

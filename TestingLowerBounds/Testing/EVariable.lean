/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Convex
import TestingLowerBounds.ForMathlib.Integrable
import TestingLowerBounds.ForMathlib.RadonNikodym

/-!

# TODO

-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : ℝ → ℝ}

structure IsEVar (f : α → ℝ≥0∞) (s : Set (Measure α)) : Prop :=
  measurable : Measurable f
  lintegral_le_one : ∀ μ ∈ s, ∫⁻ x, f x ∂μ ≤ 1

structure IsNumeraire (f : α → ℝ≥0∞) (s : Set (Measure α)) (ν : Measure α) : Prop :=
  isEVar : IsEVar f s
  maximal : ∀ g, IsEVar g s → ∫⁻ x, g x / f x ∂ν ≤ 1

lemma isEVar_rnDeriv (μ ν : Measure α) [IsProbabilityMeasure μ] [SigmaFinite ν] :
    IsEVar (∂μ/∂(μ + ν) / ∂ν/∂(μ + ν)) {ν} := by
  refine ⟨(μ.measurable_rnDeriv _).div (ν.measurable_rnDeriv _), fun ν' hν' ↦ ?_⟩
  simp only [Set.mem_singleton_iff] at hν'
  rw [hν', ← measure_univ (μ := μ)]
  calc ∫⁻ x, (∂μ/∂(μ + ν) / ∂ν/∂(μ + ν)) x ∂ν
  _ ≤ ∫⁻ x, (∂μ/∂(μ + ν)) x ∂(μ + ν) := by
    rw [← lintegral_rnDeriv_mul (_ : ν ≪ μ + ν)]
    rotate_left
    · exact ((μ.measurable_rnDeriv _).div (ν.measurable_rnDeriv _)).aemeasurable
    · rw [add_comm]
      exact Measure.AbsolutelyContinuous.add_right Measure.AbsolutelyContinuous.rfl μ
    refine lintegral_mono_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ν (μ + ν)] with a ha
    by_cases h0 : (∂ν/∂(μ + ν)) a = 0
    · simp [h0]
    · rw [Pi.div_apply, ENNReal.mul_div_cancel' h0 ha.ne]
  _ ≤ μ Set.univ := Measure.lintegral_rnDeriv_le

lemma isNumeraire_rnDeriv (μ ν : Measure α) [IsProbabilityMeasure μ] [SigmaFinite ν] :
    IsNumeraire (∂μ/∂(μ + ν) / ∂ν/∂(μ + ν)) {ν} μ where
  isEVar := isEVar_rnDeriv μ ν
  maximal g hg := by
    calc ∫⁻ x, g x / (∂μ/∂(μ + ν) / ∂ν/∂(μ + ν)) x ∂μ
    _ ≤ ∫⁻ x, (∂ν/∂(μ + ν)) x * g x ∂(μ + ν) := by
      rw [← lintegral_rnDeriv_mul (_ : μ ≪ μ + ν)]
      rotate_left
      · exact (hg.measurable.div
          ((μ.measurable_rnDeriv _).div (ν.measurable_rnDeriv _))).aemeasurable
      · exact Measure.AbsolutelyContinuous.add_right Measure.AbsolutelyContinuous.rfl ν
      refine lintegral_mono_ae ?_
      filter_upwards [Measure.rnDeriv_lt_top μ (μ + ν)] with a ha
      by_cases h0 : (∂μ/∂(μ + ν)) a = 0
      · simp [h0]
      · rw [Pi.div_apply, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (.inr ha.ne) (.inr h0), inv_inv, mul_comm _ ((∂μ/∂(μ + ν)) a)⁻¹,
          ← mul_assoc,← mul_assoc, ENNReal.mul_inv_cancel h0 ha.ne, one_mul]
    _ ≤ ∫⁻ x, g x ∂ν := by
      rw [← lintegral_rnDeriv_mul (_ : ν ≪ μ + ν)]
      · exact hg.measurable.aemeasurable
      · rw [add_comm]
        exact Measure.AbsolutelyContinuous.add_right Measure.AbsolutelyContinuous.rfl μ
    _ ≤ 1 := hg.lintegral_le_one ν (Set.mem_singleton _)

end ProbabilityTheory

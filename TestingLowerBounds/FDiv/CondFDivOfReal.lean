/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.FDiv.CondFDiv
import TestingLowerBounds.FDiv.FDivOfReal

/-!

# f-Divergences in which the DivFunction is given by DivFunction.ofReal

-/

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}
  {f : ℝ → ℝ} {hf : ConvexOn ℝ (Ioi 0) f} {hf_one : f 1 = 0}

lemma integrable_fDiv_ofReal_iff_of_ne_top [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    {f : ℝ → ℝ} {hf : ConvexOn ℝ (Set.Ioi 0) f} {hf_one : f 1 = 0}
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Set.Ioi 0) 0)
    (h_int : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (h_ne : (DivFunction.ofReal f hf hf_one).derivAtTop ≠ ∞) :
    Integrable (fun a ↦ (fDiv (.ofReal f hf hf_one) (κ a) (η a)).toReal) μ
      ↔ Integrable (fun a ↦ ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a)) μ := by
  have h : ∀ᵐ a ∂μ, (fDiv (.ofReal f hf hf_one) (κ a) (η a)).toReal
      = ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a)
        + (DivFunction.ofReal f hf hf_one).derivAtTop.toReal
          * ((κ a).singularPart (η a) .univ).toReal := by
    filter_upwards [h_int] with a h_int
    exact toReal_fDiv_ofReal_eq_integral_add' hf_nonneg h_cont h_int h_ne
  rw [integrable_congr h, integrable_add_iff_integrable_left']
  refine Integrable.const_mul ?_ _
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · simp_rw [← Kernel.singularPart_eq_singularPart_measure]
    exact (Kernel.measurable_coe _ .univ).aemeasurable
  · rw [lintegral_singularPart _ _ _ .univ]
    simp

lemma integrable_fDiv_ofReal_iff_of_ac [IsFiniteKernel κ] [IsFiniteKernel η]
    {f : ℝ → ℝ} {hf : ConvexOn ℝ (Set.Ioi 0) f} {hf_one : f 1 = 0}
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Set.Ioi 0) 0)
    (h_int : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (hμη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun a ↦ (fDiv (.ofReal f hf hf_one) (κ a) (η a)).toReal) μ
      ↔ Integrable (fun a ↦ ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a)) μ := by
  have h : ∀ᵐ a ∂μ, (fDiv (.ofReal f hf hf_one) (κ a) (η a)).toReal
      = ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a) := by
    filter_upwards [h_int, hμη] with a h_int hμη
    exact toReal_fDiv_ofReal_eq_integral_add_of_ac hf_nonneg h_cont h_int hμη
  rw [integrable_congr h]

end ProbabilityTheory

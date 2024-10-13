/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.FDiv.Basic
import TestingLowerBounds.ForMathlib.RadonNikodym

/-!
# Measurability/integrability lemmas about kernels

-/

open MeasureTheory MeasurableSpace Set

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [CountableOrCountablyGenerated α β]
  {f : ℝ → ℝ}

lemma measurableSet_integrable_f_kernel_rnDeriv (κ η ξ : Kernel α β) [IsFiniteKernel ξ]
    (hf : StronglyMeasurable f) :
    MeasurableSet {a | Integrable (fun x ↦ f (κ.rnDeriv η a x).toReal) (ξ a)} :=
  measurableSet_kernel_integrable
    (hf.comp_measurable (κ.measurable_rnDeriv η).ennreal_toReal)

lemma measurableSet_integrable_f_rnDeriv (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    (hf : StronglyMeasurable f) :
    MeasurableSet {a | Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a)} := by
  convert measurableSet_integrable_f_kernel_rnDeriv κ η η hf using 3 with a
  refine integrable_congr ?_
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure] with b hb
  rw [hb]

lemma measurable_integral_f_rnDeriv (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    (hf : StronglyMeasurable f) :
    Measurable fun a ↦ ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a) := by
  have : ∀ a, ∫ x, f ((∂κ a/∂η a) x).toReal ∂η a
      = ∫ x, f (κ.rnDeriv η a x).toReal ∂η a := by
    refine fun a ↦ integral_congr_ae ?_
    filter_upwards [κ.rnDeriv_eq_rnDeriv_measure] with x hx
    rw [hx]
  simp_rw [this]
  refine (StronglyMeasurable.integral_kernel_prod_left ?_).measurable
  refine hf.comp_measurable ?_
  exact ((κ.measurable_rnDeriv η).comp measurable_swap).ennreal_toReal

lemma measurable_fDiv (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    (hf : StronglyMeasurable f) :
    Measurable (fun a ↦ fDiv f (κ a) (η a)) := by
  let s := {a | Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a)}
  have hs : MeasurableSet s := measurableSet_integrable_f_rnDeriv κ η hf
  classical
  have h_eq : (fun a ↦ fDiv f (κ a) (η a))
      = fun a ↦ if a ∈ s then ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a)
          + derivAtTop f * (κ a).singularPart (η a) .univ
        else ⊤ := by
    ext a
    split_ifs with ha
    · rw [fDiv_of_integrable ha]
    · rw [fDiv_of_not_integrable ha]
  rw [h_eq]
  refine Measurable.ite hs ?_ measurable_const
  refine Measurable.add ?_ ?_
  · exact (measurable_integral_f_rnDeriv _ _ hf).coe_real_ereal
  · refine Measurable.const_mul ?_ _
    exact ((Measure.measurable_coe .univ).comp (κ.measurable_singularPart η)).coe_ereal_ennreal

end ProbabilityTheory

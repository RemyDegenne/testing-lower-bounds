/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import TestingLowerBounds.FDiv.Basic
public import TestingLowerBounds.ForMathlib.RadonNikodym

/-!
# Measurability of f-divergences between kernels

-/

@[expose] public section

open MeasureTheory MeasurableSpace Set

open scoped ENNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [CountableOrCountablyGenerated α β]
  {f : DivFunction}

lemma measurable_lintegral_f_kernel_rnDeriv (κ η ξ : Kernel α β) [IsSFiniteKernel ξ] :
    Measurable fun a ↦ ∫⁻ x, f (κ.rnDeriv η a x) ∂(ξ a) := by
  refine Measurable.lintegral_kernel_prod_right ?_
  exact f.measurable.comp (κ.measurable_rnDeriv η)

lemma measurable_lintegral_f_rnDeriv (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable fun a ↦ ∫⁻ x, f ((∂κ a/∂η a) x) ∂(η a) := by
  convert measurable_lintegral_f_kernel_rnDeriv κ η η using 2 with a
  · rw [lintegral_congr_ae ?_]
    filter_upwards [κ.rnDeriv_eq_rnDeriv_measure] with b hb
    rw [hb]

lemma measurable_fDiv (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦ fDiv f (κ a) (η a)) :=
  (measurable_lintegral_f_rnDeriv κ η).add
    (((Measure.measurable_coe .univ).comp (κ.measurable_singularPart η)).const_mul _)

end ProbabilityTheory

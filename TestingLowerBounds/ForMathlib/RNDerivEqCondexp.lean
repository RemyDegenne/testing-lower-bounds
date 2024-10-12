/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.ForMathlib.RadonNikodym

/-!
# Radon-Nikodym derivative of the composition of a measure and a kernel

-/

open MeasureTheory MeasurableSpace Set

open scoped ENNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}

lemma toReal_rnDeriv_map [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    {g : α → β} (hg : Measurable g) :
    (fun a ↦ ((μ.map g).rnDeriv (ν.map g) (g a)).toReal)
      =ᵐ[ν] ν[(fun a ↦ (μ.rnDeriv ν a).toReal) | mβ.comap g] := by
  refine ae_eq_condexp_of_forall_setIntegral_eq ?_ ?_ ?_ ?_ ?_
  · exact measurable_iff_comap_le.mp hg
  · exact Measure.integrable_toReal_rnDeriv
  · rintro _ ⟨t, _, rfl⟩ _
    refine Integrable.integrableOn ?_
    change Integrable ((fun x ↦ ((∂Measure.map g μ/∂Measure.map g ν) x).toReal) ∘ g) ν
    rw [← integrable_map_measure (f := g)]
    · exact Measure.integrable_toReal_rnDeriv
    · exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.aestronglyMeasurable
    · exact hg.aemeasurable
  · rintro _ ⟨t, ht, rfl⟩ _
    calc ∫ x in g ⁻¹' t, ((∂μ.map g/∂ν.map g) (g x)).toReal ∂ν
      = ∫ y in t, ((∂μ.map g/∂ν.map g) y).toReal ∂(ν.map g) := by
          rw [setIntegral_map ht _ hg.aemeasurable]
          exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.aestronglyMeasurable
    _ = ∫ x in g ⁻¹' t, ((∂μ/∂ν) x).toReal ∂ν := by
          rw [Measure.setIntegral_toReal_rnDeriv (hμν.map hg),
            Measure.setIntegral_toReal_rnDeriv hμν, Measure.map_apply hg ht]
  · refine StronglyMeasurable.aeStronglyMeasurable' ?_
    refine Measurable.stronglyMeasurable ?_
    refine @Measurable.ennreal_toReal _ (mβ.comap g) _ ?_
    intro s hs
    change MeasurableSet[mβ.comap g] ((_ ∘ g) ⁻¹' s)
    rw [preimage_comp]
    suffices MeasurableSet (∂Measure.map g μ/∂Measure.map g ν ⁻¹' s) by exact ⟨_, this, rfl⟩
    exact Measure.measurable_rnDeriv _ _ hs

end ProbabilityTheory

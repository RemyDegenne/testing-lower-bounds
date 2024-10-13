/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.ForMathlib.RadonNikodym
import TestingLowerBounds.MeasureCompProd

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
    refine (@Measurable.ennreal_toReal _ (mβ.comap g) _ (fun s hs ↦ ?_)).stronglyMeasurable
    exact ⟨_, Measure.measurable_rnDeriv _ _ hs, rfl⟩

lemma toReal_rnDeriv_comp_eq_condexp_compProd [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    [IsFiniteKernel κ] [IsFiniteKernel η] (hκη : ∀ᵐ x ∂μ, κ x ≪ η x) :
    (fun ab ↦ ((κ ∘ₘ μ).rnDeriv (η ∘ₘ ν) ab.2).toReal)
      =ᵐ[ν ⊗ₘ η] (ν ⊗ₘ η)[fun ab ↦ ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) ab).toReal | mβ.comap Prod.snd] := by
  have h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η := Measure.absolutelyContinuous_compProd hμν hκη
  refine Filter.EventuallyEq.trans ?_ (toReal_rnDeriv_map h_ac measurable_snd)
  refine ae_of_all _ (fun ab ↦ ?_)
  simp only
  congr <;> rw [← Measure.snd, Measure.snd_compProd]

lemma toReal_rnDeriv_comp [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    [IsFiniteKernel κ] :
    (fun ab ↦ ((κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν) ab.2).toReal)
      =ᵐ[ν ⊗ₘ κ] (ν ⊗ₘ κ)[fun ab ↦ (μ.rnDeriv ν ab.1).toReal | mβ.comap Prod.snd] := by
  refine (toReal_rnDeriv_comp_eq_condexp_compProd hμν ?_).trans ?_
  · exact ae_of_all _ (fun x ↦ Measure.AbsolutelyContinuous.rfl)
  have h_eq := Kernel.rnDeriv_measure_compProd_left μ ν κ
  refine condexp_congr_ae ?_
  filter_upwards [h_eq] with x hx
  rw [hx]

end ProbabilityTheory

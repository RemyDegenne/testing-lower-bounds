/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.ForMathlib.RadonNikodym
import TestingLowerBounds.ForMathlib.RnDeriv
import TestingLowerBounds.MeasureCompProd

/-!
# Radon-Nikodym derivative of the composition of a measure and a kernel

-/

open MeasureTheory MeasurableSpace Set

open scoped ENNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}

lemma toReal_rnDeriv_comp_eq_condexp_compProd [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    [IsFiniteKernel κ] [IsFiniteKernel η] (hκη : ∀ᵐ x ∂μ, κ x ≪ η x) :
    (fun ab ↦ ((κ ∘ₘ μ).rnDeriv (η ∘ₘ ν) ab.2).toReal)
      =ᵐ[ν ⊗ₘ η] (ν ⊗ₘ η)[fun ab ↦ ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) ab).toReal | mβ.comap Prod.snd] := by
  have h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η := Measure.absolutelyContinuous_compProd hμν hκη
  refine Filter.EventuallyEq.trans ?_ (Measure.toReal_rnDeriv_map h_ac measurable_snd)
  refine ae_of_all _ (fun ab ↦ ?_)
  simp only
  congr <;> rw [← Measure.snd, Measure.snd_compProd]

lemma toReal_rnDeriv_comp_eq_condexp_compProd_right [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (κ : Kernel α β) [IsFiniteKernel κ] :
    (fun ab ↦ ((κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν) ab.2).toReal)
      =ᵐ[ν ⊗ₘ κ] (ν ⊗ₘ κ)[fun ab ↦ ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) ab).toReal | mβ.comap Prod.snd] := by
  refine toReal_rnDeriv_comp_eq_condexp_compProd hμν ?_
  exact ae_of_all _ (fun x ↦ Measure.AbsolutelyContinuous.rfl)

lemma toReal_rnDeriv_comp [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    [IsFiniteKernel κ] :
    (fun ab ↦ ((κ ∘ₘ μ).rnDeriv (κ ∘ₘ ν) ab.2).toReal)
      =ᵐ[ν ⊗ₘ κ] (ν ⊗ₘ κ)[fun ab ↦ (μ.rnDeriv ν ab.1).toReal | mβ.comap Prod.snd] := by
  refine (toReal_rnDeriv_comp_eq_condexp_compProd_right hμν κ).trans (condexp_congr_ae ?_)
  filter_upwards [Kernel.rnDeriv_measure_compProd_left μ ν κ] with x hx
  rw [hx]

theorem _root_.Measurable.setLIntegral_kernel_prod_right' [IsSFiniteKernel κ]
    {f : α × β → ℝ≥0∞} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => ∫⁻ b in s, f (a, b) ∂κ a := by
  simp_rw [← Kernel.lintegral_restrict κ hs]; exact hf.lintegral_kernel_prod_right'

end ProbabilityTheory

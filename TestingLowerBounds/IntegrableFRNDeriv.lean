/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import TestingLowerBounds.Convex
public import TestingLowerBounds.DerivAtTop
public import TestingLowerBounds.ForMathlib.RnDeriv
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Integrability of `f ∘ ∂μ/∂ν`

For finite measures `μ, ν` and a convex function `f` on `[0, ∞)` with `derivAtTop f ≠ ⊤`, the
function `x ↦ f (∂μ/∂ν x).toReal` is `ν`-integrable (`integrable_f_rnDeriv_of_derivAtTop_ne_top`):
it lies between an affine function of `∂μ/∂ν` and `f 0 + (derivAtTop f).toReal * ∂μ/∂ν`.

-/

@[expose] public section

namespace MeasureTheory

lemma integrable_f_rnDeriv_of_derivAtTop_ne_top {α : Type*} {mα : MeasurableSpace α}
    {f : ℝ → ℝ} (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_deriv : derivAtTop f ≠ ⊤) :
    Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, _ → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun x ↦ f (μ.rnDeriv ν x).toReal)
    (g₁ := fun x ↦ c * (μ.rnDeriv ν x).toReal + c')
    (g₂ := fun x ↦ (derivAtTop f).toReal * (μ.rnDeriv ν x).toReal + f 0)
    ?_ ?_ ?_ ?_ ?_
  · exact (hf.comp_measurable (μ.measurable_rnDeriv ν).ennreal_toReal).aestronglyMeasurable
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · refine ae_of_all _ (fun x ↦ ?_)
    have h := le_add_derivAtTop'' hf_cvx hf_deriv le_rfl
      (ENNReal.toReal_nonneg : 0 ≤ (μ.rnDeriv ν x).toReal)
    rwa [zero_add, add_comm] at h
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    exact Measure.integrable_toReal_rnDeriv
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    exact Measure.integrable_toReal_rnDeriv

end MeasureTheory

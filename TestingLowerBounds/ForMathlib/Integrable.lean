/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!

# Integrability results

-/

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

lemma lintegral_ofReal_eq_top_of_not_integrable_of_nonneg {f : α → ℝ}
    (hfm : AEStronglyMeasurable f μ) (h_int : ¬ Integrable f μ) (hf : 0 ≤ᵐ[μ] f) :
    ∫⁻ a, ENNReal.ofReal (f a) ∂μ = ∞ := by
  simp_rw [Integrable, hfm, hasFiniteIntegral_iff_norm, lt_top_iff_ne_top, Ne, true_and,
      Classical.not_not] at h_int
  have : ∫⁻ a : α, ENNReal.ofReal (f a) ∂μ = ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ := by
    refine lintegral_congr_ae (hf.mono fun a h => ?_)
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg h]
  rw [this, h_int]

lemma lintegral_ofReal_ne_top_iff_integrable_of_nonneg {f : α → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) :
    ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≠ ∞ ↔ Integrable f μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra h_int
    exact h (lintegral_ofReal_eq_top_of_not_integrable_of_nonneg hfm h_int hf)
  · rw [← ofReal_integral_eq_lintegral_ofReal h hf]
    exact ENNReal.ofReal_ne_top

lemma Integrable.rnDeriv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν)
    [SigmaFinite μ] {f : α → E} (hf : Integrable f μ) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal • f x) ν :=
  (integrable_rnDeriv_smul_iff hμν).mpr hf

end MeasureTheory

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

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

lemma integrable_toReal_iff {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    Integrable (fun x ↦ (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ ≠ ∞ := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrable_toReal_of_lintegral_ne_top hf h⟩
  rw [Integrable, HasFiniteIntegral] at h
  have : ∀ᵐ x ∂μ, f x = ↑‖(f x).toReal‖₊ := by
    filter_upwards [hf_ne_top] with x hx
    rw [← ofReal_norm_eq_coe_nnnorm, Real.norm_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hx]
  rw [lintegral_congr_ae this]
  exact h.2.ne

theorem Integrable.neg' [NormedAddCommGroup β]
    {f : α → β} (hf : Integrable f μ) : Integrable (fun x ↦ - f x) μ :=
  ⟨hf.aestronglyMeasurable.neg, hf.hasFiniteIntegral.neg⟩

@[simp]
lemma integrable_add_iff_integrable_left' [NormedAddCommGroup β]
    {f g : α → β} (hf : Integrable f μ) :
    Integrable (fun x ↦ g x + f x) μ ↔ Integrable g μ :=
  integrable_add_iff_integrable_left hf

@[simp]
lemma integrable_add_iff_integrable_right' [NormedAddCommGroup β]
    {f g : α → β} (hf : Integrable f μ) :
    Integrable (fun x ↦ f x + g x) μ ↔ Integrable g μ :=
  integrable_add_iff_integrable_right hf

lemma Integrable.rnDeriv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν)
    [SigmaFinite μ] {f : α → E} (hf : Integrable f μ) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal • f x) ν :=
  (integrable_rnDeriv_smul_iff hμν).mpr hf

lemma integrable_of_le_of_le {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {f g₁ g₂ : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (h_le₁ : g₁ ≤ᵐ[μ] f) (h_le₂ : f ≤ᵐ[μ] g₂)
    (h_int₁ : Integrable g₁ μ) (h_int₂ : Integrable g₂ μ) :
    Integrable f μ := by
  have : ∀ᵐ x ∂μ, ‖f x‖ ≤ max ‖g₁ x‖ ‖g₂ x‖ := by
    filter_upwards [h_le₁, h_le₂] with x hx1 hx2
    simp only [Real.norm_eq_abs]
    exact abs_le_max_abs_abs hx1 hx2
  have h_le_add : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖‖g₁ x‖ + ‖g₂ x‖‖ := by
    filter_upwards [this] with x hx
    refine hx.trans ?_
    conv_rhs => rw [Real.norm_of_nonneg (by positivity)]
    exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
  exact Integrable.mono (h_int₁.norm.add h_int₂.norm) hf h_le_add

end MeasureTheory

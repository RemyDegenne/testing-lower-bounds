/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Function.L1Space

/-!

# Integrability results

-/

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {μ : Measure α}

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

end MeasureTheory

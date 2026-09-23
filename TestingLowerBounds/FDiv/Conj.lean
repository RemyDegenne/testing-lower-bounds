/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import TestingLowerBounds.FDiv.Basic
public import TestingLowerBounds.FDiv.DivFunction.Conj

/-! # f-Divergence of the conjugate divergence function

The main result is `fDiv_conj`: `fDiv f.conj μ ν = fDiv f ν μ`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {f : DivFunction}

/-- On the set where `∂μ/∂ν` does not vanish, `∂ν/∂μ` is its inverse, `ν`-almost everywhere. -/
lemma _root_.MeasureTheory.Measure.rnDeriv_eq_inv_rnDeriv_of_ne_zero (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] :
    ∀ᵐ x ∂ν, (∂μ/∂ν) x ≠ 0 → (∂ν/∂μ) x = ((∂μ/∂ν) x)⁻¹ := by
  have h1 : (∂(ν.withDensity (∂μ/∂ν))/∂ν)⁻¹ =ᵐ[ν.withDensity (∂μ/∂ν)] ∂ν/∂(ν.withDensity (∂μ/∂ν)) :=
    Measure.inv_rnDeriv (μ := ν.withDensity (∂μ/∂ν)) (ν := ν)
      (withDensity_absolutelyContinuous ν (∂μ/∂ν))
  have h2 := Measure.rnDeriv_withDensity ν (Measure.measurable_rnDeriv μ ν)
  have h3 : ∂ν/∂μ =ᵐ[ν.withDensity (∂μ/∂ν)] ∂ν/∂(ν.withDensity (∂μ/∂ν)) := by
    have := Measure.rnDeriv_add_right_of_mutuallySingular (μ := ν) (ν := ν.withDensity (∂μ/∂ν))
      (Measure.mutuallySingular_singularPart μ ν).symm.withDensity
    rwa [add_comm, ← μ.haveLebesgueDecomposition_add ν] at this
  rw [Filter.EventuallyEq, ae_withDensity_iff (Measure.measurable_rnDeriv _ _)] at h1 h3
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3 hx0
  rw [hx3 hx0, ← hx1 hx0, Pi.inv_apply, hx2]

/-- Decomposition of `∫⁻ x, g x ∂ν` along the Lebesgue decomposition of `ν` with respect to `μ`. -/
lemma _root_.MeasureTheory.lintegral_eq_add_singularPart_withDensity (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] (g : α → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x, g x ∂ν = ∫⁻ x, g x ∂(ν.singularPart μ) + ∫⁻ x, (∂ν/∂μ) x * g x ∂μ := by
  have h := lintegral_add_measure g (ν.singularPart μ) (μ.withDensity (∂ν/∂μ))
  rw [← ν.haveLebesgueDecomposition_add μ,
    lintegral_withDensity_eq_lintegral_mul _ (Measure.measurable_rnDeriv _ _) hg] at h
  exact h

/-- The f-divergence for the conjugate function `f.conj` is the f-divergence for `f` with the
measures swapped. -/
lemma fDiv_conj (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    fDiv f.conj μ ν = fDiv f ν μ := by
  have h_left : ∫⁻ x, f.conj ((∂μ/∂ν) x) ∂ν
      = f.derivAtTop * ν.singularPart μ univ + ∫⁻ x, (∂ν/∂μ) x * f.conj ((∂μ/∂ν) x) ∂μ := by
    rw [lintegral_eq_add_singularPart_withDensity μ ν _ measurable_divFunction_rnDeriv]
    congr 1
    have h : (fun x ↦ f.conj ((∂μ/∂ν) x)) =ᵐ[ν.singularPart μ] fun _ ↦ f.derivAtTop := by
      filter_upwards [Measure.rnDeriv_eq_zero_ae_singularPart μ ν] with x hx
      simp [hx]
    rw [lintegral_congr_ae h, lintegral_const]
  have h_right : ∫⁻ x, f ((∂ν/∂μ) x) ∂μ
      = f 0 * μ.singularPart ν univ + ∫⁻ x, (∂μ/∂ν) x * f ((∂ν/∂μ) x) ∂ν := by
    rw [lintegral_eq_add_singularPart_withDensity ν μ _ measurable_divFunction_rnDeriv]
    congr 1
    have h : (fun x ↦ f ((∂ν/∂μ) x)) =ᵐ[μ.singularPart ν] fun _ ↦ f 0 := by
      filter_upwards [Measure.rnDeriv_eq_zero_ae_singularPart ν μ] with x hx
      simp [hx]
    rw [lintegral_congr_ae h, lintegral_const]
  have h_key : ∫⁻ x, (∂ν/∂μ) x * f.conj ((∂μ/∂ν) x) ∂μ
      = ∫⁻ x, (∂μ/∂ν) x * f ((∂ν/∂μ) x) ∂ν := by
    rw [lintegral_eq_add_singularPart_withDensity ν μ (fun x ↦ (∂ν/∂μ) x * f.conj ((∂μ/∂ν) x))
      ((Measure.measurable_rnDeriv _ _).mul measurable_divFunction_rnDeriv)]
    have h0 : ∫⁻ x, (∂ν/∂μ) x * f.conj ((∂μ/∂ν) x) ∂(μ.singularPart ν) = 0 := by
      have h : (fun x ↦ (∂ν/∂μ) x * f.conj ((∂μ/∂ν) x)) =ᵐ[μ.singularPart ν] fun _ ↦ 0 := by
        filter_upwards [Measure.rnDeriv_eq_zero_ae_singularPart ν μ] with x hx
        simp [hx]
      rw [lintegral_congr_ae h, lintegral_zero]
    rw [h0, zero_add]
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_eq_inv_rnDeriv_of_ne_zero μ ν, Measure.rnDeriv_ne_top μ ν]
      with x hx hx_top
    by_cases h0 : (∂μ/∂ν) x = 0
    · simp [h0]
    rw [hx h0, DivFunction.conj_of_ne_zero h0, ← mul_assoc, ENNReal.mul_inv_cancel h0 hx_top,
      one_mul]
  rw [fDiv, fDiv, DivFunction.derivAtTop_conj, h_left, h_right, h_key]
  ring

end ProbabilityTheory

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import TestingLowerBounds.FDiv.Basic
public import TestingLowerBounds.FDiv.DivFunction.CompAffine
public import TestingLowerBounds.FDiv.DivFunction.Conj

/-! # f-Divergence of the conjugate divergence function

The main result is `fDiv_conj`: `fDiv f.conj μ ν = fDiv f ν μ`.

We then describe the f-divergences involving mixtures `a • μ + b • ν` (with `a + b = 1`) as
f-divergences between `μ` and `ν` for modified divergence functions:
* `fDiv_smul_add_smul_left`: `fDiv f (a • μ + b • ν) ν = fDiv (f.compAffine a b _) μ ν`.
* `fDiv_smul_add_smul_right`: `fDiv f μ (a • μ + b • ν)`, for the function
  `x ↦ (a * x + b) * f (x / (a * x + b))`.
* `fDiv_smul_add_smul_right'`: `fDiv f ν (a • μ + b • ν)`, for the function
  `x ↦ (a * x + b) * f (1 / (a * x + b))`.
-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal

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

section Mixture

variable {a b : ℝ≥0}

/-- `fDiv f (a • μ + b • ν) ν` is the f-divergence between `μ` and `ν` for the function
`x ↦ f (a * x + b)`. -/
lemma fDiv_smul_add_smul_left (hab : a + b = 1) (μ ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] :
    fDiv f (a • μ + b • ν) ν = fDiv (f.compAffine a b hab) μ ν := by
  have h_rn : (fun x ↦ f ((∂(a • μ + b • ν)/∂ν) x)) =ᵐ[ν] fun x ↦ f (a * (∂μ/∂ν) x + b) := by
    filter_upwards [Measure.rnDeriv_add' (a • μ) (b • ν) ν, Measure.rnDeriv_smul_left' μ ν a,
      Measure.rnDeriv_smul_left' ν ν b, ν.rnDeriv_self] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4]
    simp [ENNReal.smul_def]
  have h_sing : (a • μ + b • ν).singularPart ν = a • μ.singularPart ν := by
    rw [Measure.singularPart_add, Measure.singularPart_smul, Measure.singularPart_smul,
      Measure.singularPart_self, smul_zero, add_zero]
  rw [fDiv, fDiv, lintegral_congr_ae h_rn, h_sing, DivFunction.derivAtTop_compAffine]
  simp only [DivFunction.compAffine_apply, Measure.coe_nnreal_smul_apply]
  ring

/-- `fDiv f ν (a • μ + b • ν)` is the f-divergence between `μ` and `ν` for the function
`x ↦ (a * x + b) * f (1 / (a * x + b))`. -/
lemma fDiv_smul_add_smul_right' (hab : a + b = 1) (μ ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] :
    fDiv f ν (a • μ + b • ν) = fDiv (f.conj.compAffine a b hab) μ ν := by
  rw [← fDiv_conj, fDiv_smul_add_smul_left]

/-- `fDiv f μ (a • μ + b • ν)` is the f-divergence between `μ` and `ν` for the function
`x ↦ (a * x + b) * f (x / (a * x + b))`. -/
lemma fDiv_smul_add_smul_right (hab : a + b = 1) (μ ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] :
    fDiv f μ (a • μ + b • ν)
      = fDiv (f.conj.compAffine b a (by rwa [add_comm])).conj μ ν := by
  rw [← fDiv_conj, add_comm, fDiv_smul_add_smul_left, fDiv_conj]

lemma smul_add_ne_zero (hab : a + b = 1) {x : ℝ≥0∞} (hx0 : x ≠ 0) : (a : ℝ≥0∞) * x + b ≠ 0 := by
  intro h
  rw [add_eq_zero, mul_eq_zero] at h
  obtain ⟨ha | hx, hb⟩ := h
  · simp_all
  · exact hx0 hx

/-- Value of the divergence function of `fDiv_smul_add_smul_right'` away from `0`. -/
lemma conj_compAffine_apply (hab : a + b = 1) {x : ℝ≥0∞} (hx0 : x ≠ 0) :
    f.conj.compAffine a b hab x = (a * x + b) * f (a * x + b)⁻¹ := by
  rw [DivFunction.compAffine_apply, DivFunction.conj_of_ne_zero (smul_add_ne_zero hab hx0)]

/-- Value of the divergence function of `fDiv_smul_add_smul_right` away from `0` and `∞`. -/
lemma conj_compAffine_conj_apply (hab : a + b = 1) {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx : x ≠ ∞) :
    (f.conj.compAffine b a (by rwa [add_comm])).conj x = (a * x + b) * f (x / (a * x + b)) := by
  have hx_inv : x⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hx
  have hx_inv' : x⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hx0
  have h_eq : (b : ℝ≥0∞) * x⁻¹ + a = x⁻¹ * (a * x + b) := by
    rw [mul_add, ← mul_assoc, mul_comm x⁻¹, mul_assoc, ENNReal.inv_mul_cancel hx0 hx, mul_one,
      add_comm, mul_comm]
  have h0 : (b : ℝ≥0∞) * x⁻¹ + a ≠ 0 := by
    rw [h_eq]
    exact mul_ne_zero hx_inv (smul_add_ne_zero hab hx0)
  rw [DivFunction.conj_of_ne_zero hx0, DivFunction.compAffine_apply,
    DivFunction.conj_of_ne_zero h0, h_eq, ← mul_assoc, ← mul_assoc,
    ENNReal.mul_inv_cancel hx0 hx, one_mul, ENNReal.mul_inv (Or.inl hx_inv) (Or.inl hx_inv'),
    inv_inv, div_eq_mul_inv]

end Mixture

end ProbabilityTheory

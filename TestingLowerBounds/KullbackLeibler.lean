/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import TestingLowerBounds.FDiv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Kullback-Leibler divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real MeasureTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

section move_this

lemma integrable_rnDeriv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν)
    [SigmaFinite μ] {f : α → E} (hf : Integrable f μ) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal • f x) ν :=
  (integrable_rnDeriv_smul_iff hμν).mpr hf

end move_this

open Classical in
/-- Kullback-Leibler divergence between two measures, real-valued version.

We test `μ ≪ ν` to ensure that this definition is 0 whenever the informal KL should be ∞. -/
noncomputable def klReal (μ ν : Measure α) : ℝ :=
  if μ ≪ ν then ∫ x, llr μ ν x ∂μ else 0

open Classical in
/-- Kullback-Leibler divergence between two measures. -/
noncomputable
def kl (μ ν : Measure α) : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, llr μ ν x ∂μ) else ∞

lemma klReal_of_ac (h : μ ≪ ν) : klReal μ ν = ∫ x, llr μ ν x ∂μ := if_pos h

@[simp]
lemma klReal_of_not_ac (h : ¬ μ ≪ ν) : klReal μ ν = 0 := if_neg h

@[simp]
lemma klReal_of_not_integrable (h : ¬ Integrable (llr μ ν) μ) : klReal μ ν = 0 := by
  by_cases h_ac : μ ≪ ν
  · rw [klReal_of_ac h_ac, integral_undef h]
  · exact if_neg h_ac

section llr_and_lrf

lemma integrable_rnDeriv_mul_log [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal) ν :=
  integrable_rnDeriv_smul hμν h_int

lemma klReal_eq_fDiv_mul_log [SigmaFinite μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) :
    klReal μ ν = fDiv (fun x ↦ x * log x) μ ν := by
  /-simp_rw [klReal_of_ac hμν, llr, fDiv]
  conv_lhs =>
    rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    conv in (Measure.rnDeriv (ν.withDensity (μ.rnDeriv ν)) ν) =>
      rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
  have h_rn_eq : μ.rnDeriv ν =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toNNReal := by
    filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
    rw [ENNReal.coe_toNNReal]
    exact hx.ne
  have h_ν_eq : ν.withDensity (μ.rnDeriv ν)
      = ν.withDensity (fun x ↦ (μ.rnDeriv ν x).toNNReal) := withDensity_congr_ae h_rn_eq
  conv_lhs => rw [h_ν_eq]
  rw [integral_withDensity_eq_integral_smul]
  swap; · exact (Measure.measurable_rnDeriv _ _).ennreal_toNNReal
  congr -/
  sorry

end llr_and_lrf

section klReal_nonneg

lemma klReal_ge_mul_log' [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    (μ Set.univ).toReal * log (μ Set.univ).toReal ≤ klReal μ ν :=
  sorry
  /-(le_fDiv Real.convexOn_mul_log Real.continuous_mul_log.continuousOn
    (integrable_rnDeriv_mul_log hμν h_int) hμν).trans_eq (klReal_eq_fDiv_mul_log hμν).symm-/

lemma klReal_ge_mul_log [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    (μ Set.univ).toReal * log ((μ Set.univ).toReal / (ν Set.univ).toReal) ≤ klReal μ ν := by
  by_cases hμ : μ = 0
  · simp [klReal, hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    apply? says exact Measure.measure_univ_eq_zero.mp (hμν rfl)
  let ν' := (ν Set.univ)⁻¹ • ν
  have : IsProbabilityMeasure ν' := by
    constructor
    simp only [ν', Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ENNReal.mul_inv_cancel]
    · simp [hν]
    · exact measure_ne_top _ _
  have h := klReal_ge_mul_log' (?_ : μ ≪ ν') ?_
  rotate_left
  · refine Measure.AbsolutelyContinuous.trans hμν (Measure.absolutelyContinuous_smul ?_)
    simp [measure_ne_top ν]
  · rw [integrable_congr (llr_smul_right hμν (ν Set.univ)⁻¹ _ _)]
    rotate_left
    · simp [measure_ne_top ν _]
    · simp [hν]
    exact h_int.sub (integrable_const _)
  rw [klReal_of_ac, integral_congr_ae (llr_smul_right hμν (ν Set.univ)⁻¹ _ _)] at h
  rotate_left
  · simp [measure_ne_top ν _]
  · simp [hν]
  · refine hμν.trans (Measure.absolutelyContinuous_smul ?_)
    simp [measure_ne_top ν]
  rw [integral_sub h_int (integrable_const _), integral_const, smul_eq_mul, le_sub_iff_add_le,
    ENNReal.toReal_inv, log_inv, mul_neg, ← sub_eq_add_neg] at h
  rwa [klReal_of_ac hμν, log_div, mul_sub]
  · rw [ENNReal.toReal_ne_zero]
    simp [hμ, measure_ne_top μ]
  · rw [ENNReal.toReal_ne_zero]
    simp [hν, measure_ne_top ν]

lemma klReal_nonneg (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ klReal μ ν := by
  sorry
  /- by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [klReal_eq_fDiv_mul_log hμν]
    exact fDiv_nonneg Real.convexOn_mul_log Real.continuous_mul_log.continuousOn
      (by simp) (integrable_rnDeriv_mul_log hμν h_int) hμν
  · rw [klReal_of_ac hμν, integral_undef h_int] -/

end klReal_nonneg

lemma klReal_tilted_right [IsProbabilityMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
    {f : α → ℝ} (hfμ : Integrable f μ) (hf : Integrable (fun x ↦ exp (f x)) ν) :
    klReal μ (ν.tilted f) = klReal μ ν - ∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) := by
  rw [klReal_of_ac, klReal_of_ac hμν]
  · exact integral_llr_tilted_right hμν hfμ hf h_int
  · exact hμν.trans (absolutelyContinuous_tilted hf)

lemma integral_sub_log_integral_exp_le_klReal [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
    (f : α → ℝ) (hfμ : Integrable f μ) (hf : Integrable (fun x ↦ exp (f x)) ν) :
    ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) ≤ klReal μ ν := by
  have : klReal μ ν - klReal μ (ν.tilted f) = ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) := by
    rw [klReal_tilted_right hμν h_int hfμ hf]
    abel
  rw [← this]
  simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
  have : IsProbabilityMeasure (Measure.tilted ν f) := isProbabilityMeasure_tilted hf
  exact klReal_nonneg _ _

/-- One side of the Donsker-Varadhan variational formula for the Kullback-Leibler divergence.
See `klReal_eq_ciSup` for the equality. -/
lemma ciSup_le_klReal [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ⨆ (f : α → ℝ) (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν)
      ≤ klReal μ ν := by
  refine ciSup_le (fun f ↦ ?_)
  by_cases hfμ : Integrable f μ
  · simp only [hfμ, ciSup_unique]
    by_cases hf : Integrable (fun x ↦ exp (f x)) ν
    · simp only [hf, ciSup_unique]
      exact integral_sub_log_integral_exp_le_klReal hμν h_int f hfμ hf
    · simp [hf, csSup_empty]
      exact klReal_nonneg _ _
  · simp only [hfμ, csSup_empty, iSup_of_isEmpty]
    exact klReal_nonneg _ _

end ProbabilityTheory

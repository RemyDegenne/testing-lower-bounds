/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.ForMathlib.EReal
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!

# EReal-valued log likelihood ratio

## Main definitions

* `EReal.llr`: log-likelihood ratio, with value in `EReal`.

## Main statements

* `EReal.exp_llr`: `EReal.exp (EReal.llr μ ν x) = μ.rnDeriv ν x`
-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

noncomputable
def EReal.llr (μ ν : Measure α) (x : α) : EReal := ENNReal.log (μ.rnDeriv ν x)

lemma EReal.llr_def (μ ν : Measure α) : EReal.llr μ ν = fun x ↦ ENNReal.log (μ.rnDeriv ν x) := rfl

lemma EReal.exp_llr (μ ν : Measure α) [SigmaFinite μ] (x : α) :
    EReal.exp (EReal.llr μ ν x) = μ.rnDeriv ν x := by simp [EReal.llr]

lemma EReal.neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    - EReal.llr μ ν =ᵐ[μ] EReal.llr ν μ := by
  filter_upwards [Measure.inv_rnDeriv hμν] with x hx
  rw [Pi.neg_apply, llr, llr, ← ENNReal.log_inv, ← hx]
  congr

lemma EReal.exp_neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (fun x ↦ EReal.exp (- EReal.llr μ ν x)) =ᵐ[μ] ν.rnDeriv μ := by
  filter_upwards [EReal.neg_llr hμν] with x hx
  rw [Pi.neg_apply] at hx
  rw [hx, EReal.exp_llr]

lemma EReal.exp_neg_llr' [SigmaFinite μ] [SigmaFinite ν] (hμν : ν ≪ μ) :
    (fun x ↦ EReal.exp (- EReal.llr μ ν x)) =ᵐ[ν] ν.rnDeriv μ := by
  filter_upwards [EReal.neg_llr hμν] with x hx
  rw [Pi.neg_apply, neg_eq_iff_eq_neg] at hx
  rw [← hx, EReal.llr, ENNReal.exp_log]

@[measurability]
lemma measurable_ereal_llr (μ ν : Measure α) : Measurable (EReal.llr μ ν) :=
  (Measure.measurable_rnDeriv μ ν).ennreal_log

@[measurability]
lemma stronglyMeasurable_ereal_llr (μ ν : Measure α) : StronglyMeasurable (EReal.llr μ ν) :=
  (measurable_ereal_llr μ ν).stronglyMeasurable

lemma EReal.llr_smul_left [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc_ne_top : c ≠ ∞) :
    EReal.llr (c • μ) ν =ᵐ[μ] fun x ↦ EReal.llr μ ν x + ENNReal.log c := by
  simp only [EReal.llr, EReal.llr_def]
  have h := Measure.rnDeriv_smul_left_of_ne_top μ ν hc_ne_top
  filter_upwards [hμν.ae_le h] with x hx_eq
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [ENNReal.log_mul_add, add_comm]

lemma EReal.llr_smul_right [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    EReal.llr μ (c • ν) =ᵐ[μ] fun x ↦ EReal.llr μ ν x - ENNReal.log c := by
  simp only [llr, llr_def]
  have h := Measure.rnDeriv_smul_right_of_ne_top μ ν hc hc_ne_top
  filter_upwards [hμν.ae_le h] with x hx_eq
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [ENNReal.log_mul_add, ENNReal.log_inv, add_comm, sub_eq_add_neg]

end MeasureTheory

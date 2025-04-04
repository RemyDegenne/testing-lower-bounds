/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.FDiv.Basic
import TestingLowerBounds.FDiv.DivFunction.OfReal

/-!

# f-Divergences in which the DivFunction is given by DivFunction.ofReal

-/

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {f g : ℝ → ℝ}

variable {hf : ConvexOn ℝ (Ioi 0) f} {hf_one : f 1 = 0}

lemma fDiv_ofReal_of_not_integrable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h : ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv (.ofReal f hf hf_one) μ ν = ∞ :=
  fDiv_of_lintegral_eq_top <|
    DivFunction.lintegral_ofReal_eq_top_of_not_integrable hf_nonneg h

lemma fDiv_ofReal_eq_integral_add [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv (.ofReal f hf hf_one) μ ν
      = ENNReal.ofReal (∫ x, f ((∂μ/∂ν) x).toReal ∂ν)
        + (DivFunction.ofReal f hf hf_one).derivAtTop * μ.singularPart ν univ := by
  rw [fDiv, DivFunction.lintegral_ofReal_eq_integral_of_continuous hf_nonneg h_cont h_int]

lemma fDiv_ofReal_eq_top_iff_of_derivAtTop_eq_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_top : (DivFunction.ofReal f hf hf_one).derivAtTop = ∞) :
    fDiv (.ofReal f hf hf_one) μ ν = ∞
      ↔ ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν ∨ ¬ μ ≪ ν := by
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · simp only [fDiv_ofReal_eq_integral_add hf_nonneg h_cont h_int, h_top, ENNReal.add_eq_top,
      ENNReal.ofReal_ne_top, ENNReal.mul_eq_top, ne_eq, ENNReal.top_ne_zero, not_false_eq_true,
      measure_ne_top, and_false, Measure.measure_univ_eq_zero, true_and, false_or, h_int,
      not_true_eq_false, Measure.singularPart_eq_zero]
  · simp [h_int, fDiv_ofReal_of_not_integrable hf_nonneg h_int]

lemma fDiv_ofReal_ne_top' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_zero : Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 ≠ ∞)
    (h_top : (DivFunction.ofReal f hf hf_one).derivAtTop ≠ ∞) :
    fDiv (.ofReal f hf hf_one) μ ν ≠ ∞ := by
  refine fDiv_ne_top_of_derivAtTop_ne_top ?_ h_top
  simp [h_zero]

lemma fDiv_ofReal_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_zero : Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 ≠ ∞)
    (h_top : limsup (fun x ↦ ENNReal.ofReal (rightDeriv f x)) atTop ≠ ∞) :
    fDiv (.ofReal f hf hf_one) μ ν ≠ ∞ :=
  fDiv_ofReal_ne_top' h_zero (DivFunction.derivAtTop_ofReal_ne_top h_top)

lemma fDiv_ofReal_eq_integral_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    fDiv (.ofReal f hf hf_one) μ ν = ENNReal.ofReal (∫ x, f ((∂μ/∂ν) x).toReal ∂ν) := by
  rw [fDiv_ofReal_eq_integral_add hf_nonneg h_cont h_int, Measure.singularPart_eq_zero_of_ac hμν]
  simp

lemma fDiv_ofReal_eq_lintegral_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    fDiv (.ofReal f hf hf_one) μ ν
      = ∫⁻ x, ENNReal.ofReal (f ((∂μ/∂ν) x).toReal) ∂ν := by
  rw [fDiv_ofReal_eq_integral_of_ac hf_nonneg h_cont h_int hμν,
    ofReal_integral_eq_lintegral_ofReal h_int]
  exact ae_of_all _ fun x ↦ hf_nonneg _ ENNReal.toReal_nonneg

lemma toReal_fDiv_ofReal_eq_integral_add' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ne : (DivFunction.ofReal f hf hf_one).derivAtTop ≠ ∞) :
    (fDiv (.ofReal f hf hf_one) μ ν).toReal
      = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν
        + (DivFunction.ofReal f hf hf_one).derivAtTop.toReal * (μ.singularPart ν univ).toReal := by
  rw [fDiv_ofReal_eq_integral_add hf_nonneg h_cont h_int, ENNReal.toReal_add, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal]
  · exact integral_nonneg (fun _ ↦ hf_nonneg _ ENNReal.toReal_nonneg)
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.mul_ne_top h_ne (measure_ne_top _ _)

lemma toReal_fDiv_ofReal_eq_integral_add_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ac : μ ≪ ν) :
    (fDiv (.ofReal f hf hf_one) μ ν).toReal = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν := by
  rw [fDiv_ofReal_eq_integral_add hf_nonneg h_cont h_int]
  simp only [Measure.singularPart_eq_zero_of_ac h_ac, Measure.coe_zero, Pi.zero_apply, mul_zero,
    add_zero, ENNReal.toReal_ofReal_eq_iff]
  exact integral_nonneg fun x ↦ hf_nonneg _ ENNReal.toReal_nonneg

lemma toReal_fDiv_ofReal_eq_integral_add [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ne : limsup (fun x ↦ ENNReal.ofReal (rightDeriv f x)) atTop ≠ ∞) :
    (fDiv (.ofReal f hf hf_one) μ ν).toReal
      = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν
        + (DivFunction.ofReal f hf hf_one).derivAtTop.toReal * (μ.singularPart ν univ).toReal := by
  rw [toReal_fDiv_ofReal_eq_integral_add' hf_nonneg h_cont h_int]
  exact DivFunction.derivAtTop_ofReal_ne_top h_ne

end ProbabilityTheory

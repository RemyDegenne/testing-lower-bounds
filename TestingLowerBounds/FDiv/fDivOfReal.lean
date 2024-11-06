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
  {hf_ld : leftDeriv f 1 ≤ 0} {hf_rd : 0 ≤ rightDeriv f 1}

lemma fDiv_ofReal_eq_integral_add [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv (.ofReal f hf hf_one hf_ld hf_rd) μ ν
      = ENNReal.ofReal (∫ x, f ((∂μ/∂ν) x).toReal ∂ν)
        + (DivFunction.ofReal f hf hf_one hf_ld hf_rd).derivAtTop * μ.singularPart ν univ := by
  rw [fDiv, DivFunction.lintegral_ofReal_eq_integral_of_continuous h_cont h_int]

lemma fDiv_ofReal_eq_integral_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    fDiv (.ofReal f hf hf_one hf_ld hf_rd) μ ν = ENNReal.ofReal (∫ x, f ((∂μ/∂ν) x).toReal ∂ν) := by
  rw [fDiv_ofReal_eq_integral_add h_cont h_int, Measure.singularPart_eq_zero_of_ac hμν]
  simp

lemma fDiv_ofReal_eq_lintegral_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    fDiv (.ofReal f hf hf_one hf_ld hf_rd) μ ν
      = ∫⁻ x, ENNReal.ofReal (f ((∂μ/∂ν) x).toReal) ∂ν := by
  rw [fDiv_ofReal_eq_integral_of_ac h_cont h_int hμν,
    ofReal_integral_eq_lintegral_ofReal h_int]
  exact ae_of_all _ fun x ↦ hf.nonneg_of_todo' hf_one hf_ld hf_rd ENNReal.toReal_nonneg

lemma toReal_fDiv_ofReal_eq_integral_add' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ne : (DivFunction.ofReal f hf hf_one hf_ld hf_rd).derivAtTop ≠ ∞) :
    (fDiv (.ofReal f hf hf_one hf_ld hf_rd) μ ν).toReal
      = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν
        + (DivFunction.ofReal f hf hf_one hf_ld hf_rd).derivAtTop.toReal
          * (μ.singularPart ν univ).toReal := by
  rw [fDiv_ofReal_eq_integral_add h_cont h_int, ENNReal.toReal_add, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal]
  · exact integral_nonneg (fun _ ↦ hf.nonneg_of_todo' hf_one hf_ld hf_rd ENNReal.toReal_nonneg)
  · exact ENNReal.ofReal_ne_top
  · refine ENNReal.mul_ne_top h_ne (measure_ne_top _ _)

lemma toReal_fDiv_ofReal_eq_integral_add [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ne : limsup (fun x ↦ ENNReal.ofReal (rightDeriv f x)) atTop ≠ ∞) :
    (fDiv (.ofReal f hf hf_one hf_ld hf_rd) μ ν).toReal
      = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν
        + (DivFunction.ofReal f hf hf_one hf_ld hf_rd).derivAtTop.toReal
          * (μ.singularPart ν univ).toReal := by
  rw [toReal_fDiv_ofReal_eq_integral_add' h_cont h_int]
  exact DivFunction.derivAtTop_ofReal_ne_top h_ne

lemma fDiv_ofReal_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_zero : Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 ≠ ⊤)
    (h_top : limsup (fun x ↦ ENNReal.ofReal (rightDeriv f x)) atTop ≠ ∞) :
    fDiv (.ofReal f hf hf_one hf_ld hf_rd) μ ν ≠ ∞ := by
  refine fDiv_ne_top_of_derivAtTop_ne_top ?_ (DivFunction.derivAtTop_ofReal_ne_top h_top)
  simp [h_zero]

end ProbabilityTheory

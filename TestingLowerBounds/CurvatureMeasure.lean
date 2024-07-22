/-
Copyright (c) 2024 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.ForMathlib.ByParts
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Probability.Notation

open MeasureTheory Set StieltjesFunction ProbabilityTheory

namespace ConvexOn

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳} {f : ℝ → ℝ} {β γ x t : ℝ}

-- Should we define this to be some junk value if f is not convex?
-- This way we could avoid having to state the convexity every time.
-- This may be put in some other place, maybe directly in the stieltjes file.
/-- The curvature measure induced by a convex function. It is defined as the only measure that has
the right derivative of the function as a CDF. -/
noncomputable
def curvatureMeasure {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) : Measure ℝ :=
  hf.rightDerivStieltjes.measure

instance {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) : IsLocallyFiniteMeasure hf.curvatureMeasure := by
  unfold curvatureMeasure
  infer_instance

/-- A Taylor formula for convex functions in terms of the right derivative
and the curvature measure. -/
theorem convex_taylor (hf : ConvexOn ℝ univ f) (hf_cont : Continuous f) {a b : ℝ} :
    f b - f a - (rightDeriv f a) * (b - a)  = ∫ x in a..b, b - x ∂(curvatureMeasure hf) := by
  have h_int : IntervalIntegrable (rightDeriv f) ℙ a b := hf.rightDeriv_mono.intervalIntegrable
  rw [← intervalIntegral.integral_eq_sub_of_hasDeriv_right hf_cont.continuousOn
    (fun x _ ↦ hf.hadDerivWithinAt_rightDeriv x) h_int]
  simp_rw [← neg_sub _ b, intervalIntegral.integral_neg, curvatureMeasure,
    mul_neg, sub_neg_eq_add, mul_comm _ (a - b)]
  let g := StieltjesFunction.id + StieltjesFunction.const (-b)
  have hg : g = fun x ↦ x - b := rfl
  rw [← hg, integral_stieltjes_meas_by_parts g hf.rightDerivStieltjes]
  simp only [Real.volume_eq_stieltjes_id, add_apply, id_apply, id_eq, const_apply, add_right_neg,
    zero_mul, zero_sub, measure_add, measure_const, add_zero, neg_sub, sub_neg_eq_add, g]
  rfl

end ConvexOn

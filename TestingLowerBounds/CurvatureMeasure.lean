/-
Copyright (c) 2024 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.ForMathlib.ByParts
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Probability.Notation
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup


open MeasureTheory Set StieltjesFunction ProbabilityTheory

namespace ConvexOn

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳} {f g : ℝ → ℝ} {β γ x t : ℝ}

--PR this to mathlib, just before `StieltjesFunction.measure_const`
@[simp]
lemma _root_.StieltjesFunction.measure_zero : StieltjesFunction.measure 0 = 0 :=
  Measure.ext_of_Ioc _ _ (fun _ _ _ ↦ by simp; rfl)

-- Should we define this to be some junk value if f is not convex?
-- This way we could avoid having to state the convexity every time.
-- This may be put in some other place, maybe directly in the stieltjes file.

open Classical in
/-- The curvature measure induced by a convex function. It is defined as the only measure that has
the right derivative of the function as a CDF. -/
noncomputable
irreducible_def curvatureMeasure (f : ℝ → ℝ) : Measure ℝ :=
  if hf : ConvexOn ℝ univ f then hf.rightDerivStieltjes.measure else 0

lemma curvatureMeasure_of_convexOn (hf : ConvexOn ℝ univ f) :
    curvatureMeasure f = hf.rightDerivStieltjes.measure := by
  rw [curvatureMeasure, dif_pos hf]

lemma curvatureMeasure_of_not_convexOn (hf : ¬ConvexOn ℝ univ f) :
    curvatureMeasure f = 0 := by
  rw [curvatureMeasure, dif_neg hf]

instance {f : ℝ → ℝ} : IsLocallyFiniteMeasure (curvatureMeasure f) := by
  simp_rw [curvatureMeasure]
  split_ifs <;> infer_instance

@[simp]
lemma curvatureMeasure_const (c : ℝ) : curvatureMeasure (fun _ ↦ c) = 0 := by
  have h : ConvexOn ℝ univ (fun (_ : ℝ) ↦ c) := convexOn_const _ convex_univ
  rw [curvatureMeasure_of_convexOn h, rightDerivStieltjes_const, StieltjesFunction.measure_zero]

@[simp]
lemma curvatureMeasure_linear (a : ℝ) : curvatureMeasure (fun x ↦ a * x) = 0 := by
  rw [curvatureMeasure_of_convexOn (const_mul a), ConvexOn.rightDerivStieltjes_linear,
    StieltjesFunction.measure_const]

lemma curvatureMeasure_add (hf : ConvexOn ℝ univ f) (hg : ConvexOn ℝ univ g) :
    curvatureMeasure (f + g) = curvatureMeasure f + curvatureMeasure g := by
  rw [curvatureMeasure_of_convexOn hf, curvatureMeasure_of_convexOn hg,
    curvatureMeasure_of_convexOn (hf.add hg), hf.rightDerivStieltjes_add hg,
    StieltjesFunction.measure_add]

@[simp]
lemma curvatureMeasure_add_const (c : ℝ) :
    curvatureMeasure (fun x ↦ f x + c) = curvatureMeasure f := by
  change (curvatureMeasure (f + fun _ ↦ c)) = curvatureMeasure f
  by_cases hf : ConvexOn ℝ univ f
  · rw [hf.curvatureMeasure_add (convexOn_const _ convex_univ), curvatureMeasure_const, add_zero]
  · rw [curvatureMeasure_of_not_convexOn hf, curvatureMeasure_of_not_convexOn]
    contrapose! hf
    have : f = f + (fun _ ↦ c) + fun _ ↦ -c := by ext x; simp
    exact this ▸ hf.add_const _

@[simp]
lemma curvatureMeasure_add_linear (a : ℝ) :
    curvatureMeasure (fun x ↦ f x + a * x) = curvatureMeasure f := by
  change (curvatureMeasure (f + fun x ↦ a * x)) = curvatureMeasure f
  by_cases hf : ConvexOn ℝ univ f
  · rw [hf.curvatureMeasure_add (const_mul a), curvatureMeasure_linear, add_zero]
  · rw [curvatureMeasure_of_not_convexOn hf, curvatureMeasure_of_not_convexOn]
    contrapose! hf
    have : f = f + (fun x ↦ a * x) + fun x ↦ (-a) * x := by ext x; simp
    exact this ▸ hf.add (const_mul _)

/-- A Taylor formula for convex functions in terms of the right derivative
and the curvature measure. -/
theorem convex_taylor (hf : ConvexOn ℝ univ f) (hf_cont : Continuous f) {a b : ℝ} :
    f b - f a - (rightDeriv f a) * (b - a)  = ∫ x in a..b, b - x ∂(curvatureMeasure f) := by
  have h_int : IntervalIntegrable (rightDeriv f) ℙ a b := hf.rightDeriv_mono.intervalIntegrable
  rw [← intervalIntegral.integral_eq_sub_of_hasDeriv_right hf_cont.continuousOn
    (fun x _ ↦ hf.hadDerivWithinAt_rightDeriv x) h_int]
  simp_rw [← neg_sub _ b, intervalIntegral.integral_neg, curvatureMeasure_of_convexOn hf,
    mul_neg, sub_neg_eq_add, mul_comm _ (a - b)]
  let g := StieltjesFunction.id + StieltjesFunction.const (-b)
  have hg : g = fun x ↦ x - b := rfl
  rw [← hg, integral_stieltjes_meas_by_parts g hf.rightDerivStieltjes]
  simp only [Real.volume_eq_stieltjes_id, add_apply, id_apply, id_eq, const_apply, add_right_neg,
    zero_mul, zero_sub, measure_add, measure_const, add_zero, neg_sub, sub_neg_eq_add, g]
  rfl

end ConvexOn

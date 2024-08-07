/-
Copyright (c) 2024 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.ForMathlib.ByParts
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Probability.Notation
-- TODO: remove this import after the next mathlib bump, now it is only needed for `ConvexOn.add_const`, but this lemma has recently been moved to `Mathlib.Analysis.Convex.Function`, which is already imported here.
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup


open MeasureTheory Set StieltjesFunction ProbabilityTheory

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳} {f g : ℝ → ℝ} {β γ x t : ℝ}

namespace StieltjesFunction

open Set Filter Function ENNReal NNReal Topology MeasureTheory
open ENNReal (ofReal)

variable (f : StieltjesFunction)

--PR this to mathlib, just before `StieltjesFunction.measure_const`
@[simp]
lemma measure_zero : StieltjesFunction.measure 0 = 0 :=
  Measure.ext_of_Ioc _ _ (fun _ _ _ ↦ by simp; rfl)


--PR this to mathlib, just after `StieltjesFunction.measure_Iic`
lemma measure_Iio {l : ℝ} (hf : Tendsto f atBot (𝓝 l)) (x : ℝ) :
    f.measure (Iio x) = ofReal (leftLim f x - l) := by
  rw [← Iic_diff_right, measure_diff _ (measurableSet_singleton x), measure_singleton,
    f.measure_Iic hf, ← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' (le_refl _))]
    <;> simp

--PR this to mathlib, just after `StieltjesFunction.measure_Ici`
lemma measure_Ioi {l : ℝ} (hf : Tendsto f atTop (𝓝 l)) (x : ℝ) :
    f.measure (Ioi x) = ofReal (l - f x) := by
  rw [← Ici_diff_left, measure_diff _ (measurableSet_singleton x), measure_singleton,
    f.measure_Ici hf, ← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' (le_refl _))]
    <;> simp

--PR this and the following lemmas to mathlib, just after `StieltjesFunction.measure_univ`
lemma measure_Ioi_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : ℝ) :
    f.measure (Ioi x) = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_atTop.mp hf (r + f x))
  exact (f.measure_Ioc x (max x N) ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
    le_tsub_of_add_le_right <| hN _ (le_max_right x N))).trans (measure_mono Ioc_subset_Ioi_self)

lemma measure_Ici_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : ℝ) :
    f.measure (Ici x) = ∞ := by
  rw [← top_le_iff, ← f.measure_Ioi_of_tendsto_atTop_atTop hf x]
  exact measure_mono Ioi_subset_Ici_self

lemma measure_Iic_of_tendsto_atBot_atBot (hf : Tendsto f atBot atBot) (x : ℝ) :
    f.measure (Iic x) = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atBot.mp (tendsto_atBot.mp hf (f x - r))
  exact (f.measure_Ioc (min x N) x ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
    le_sub_comm.mp <| hN _ (min_le_right x N))).trans (measure_mono Ioc_subset_Iic_self)

lemma measure_Iio_of_tendsto_atBot_atBot (hf : Tendsto f atBot atBot) (x : ℝ) :
    f.measure (Iio x) = ∞ := by
  rw [← top_le_iff, ← f.measure_Iic_of_tendsto_atBot_atBot hf (x - 1)]
  exact measure_mono <| Set.Iic_subset_Iio.mpr <| sub_one_lt x

lemma measure_univ_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) :
    f.measure univ = ∞ := by
  rw [← top_le_iff, ← f.measure_Ioi_of_tendsto_atTop_atTop hf 0]
  exact measure_mono fun _ _ ↦ trivial

lemma measure_univ_of_tendsto_atBot_atBot (hf : Tendsto f atBot atBot) :
    f.measure univ = ∞ := by
  rw [← top_le_iff, ← f.measure_Iio_of_tendsto_atBot_atBot hf 0]
  exact measure_mono fun _ _ ↦ trivial


end StieltjesFunction

namespace ConvexOn

open Classical in
/-- The curvature measure induced by a convex function. It is defined as the only measure that has
the right derivative of the function as a CDF.
For nonconvex functions it is defined as the zero measure. -/
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
  rw [curvatureMeasure_of_convexOn (const_mul_id a), ConvexOn.rightDerivStieltjes_linear,
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
  · rw [hf.curvatureMeasure_add (const_mul_id a), curvatureMeasure_linear, add_zero]
  · rw [curvatureMeasure_of_not_convexOn hf, curvatureMeasure_of_not_convexOn]
    contrapose! hf
    have : f = f + (fun x ↦ a * x) + fun x ↦ (-a) * x := by ext x; simp
    exact this ▸ hf.add (const_mul_id _)

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
  swap; · rw [hg]; fun_prop
  simp only [Real.volume_eq_stieltjes_id, add_apply, id_apply, id_eq, const_apply, add_right_neg,
    zero_mul, zero_sub, measure_add, measure_const, add_zero, neg_sub, sub_neg_eq_add, g]
  rfl

end ConvexOn

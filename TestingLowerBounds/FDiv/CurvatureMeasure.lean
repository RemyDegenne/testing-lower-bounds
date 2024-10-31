/-
Copyright (c) 2024 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import TestingLowerBounds.Sorry.ByParts
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import TestingLowerBounds.ForMathlib.OrderIso
import TestingLowerBounds.FDiv.DivFunction


open MeasureTheory Set StieltjesFunction

open scoped ENNReal Topology

namespace ProbabilityTheory

namespace DivFunction

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳} {f g : DivFunction} {β γ x t : ℝ}

#check Real.expOrderIso

#check ENNReal.orderIsoUnitIntervalBirational

def minmax_Ioo : Set (Icc (0 : ℝ) 1) :=
  ENNReal.orderIsoUnitIntervalBirational '' (Ioo f.xmin f.xmax)

noncomputable
def xmin_01 (f : DivFunction) : Icc (0 : ℝ) 1 := ENNReal.orderIsoUnitIntervalBirational f.xmin

lemma orderIsoUnitIntervalBirational_xmin_01 (f : DivFunction) :
    ENNReal.orderIsoUnitIntervalBirational.symm f.xmin_01 = f.xmin := by
  simp [xmin_01]

noncomputable
def xmax_01 (f : DivFunction) : Icc (0 : ℝ) 1 := ENNReal.orderIsoUnitIntervalBirational f.xmax

lemma orderIsoUnitIntervalBirational_xmax_01 (f : DivFunction) :
    ENNReal.orderIsoUnitIntervalBirational.symm f.xmax_01 = f.xmax := by
  simp [xmax_01]

noncomputable
def minmaxOrderIso (f : DivFunction) : Ioo (f.xmin_01 : ℝ) f.xmax_01 ≃o ℝ :=
  (IooOrderIsoIoo (ENNReal.orderIsoUnitIntervalBirational.lt_iff_lt.mpr xmin_lt_xmax)).trans
    IooOrderIsoReal

lemma Ioo_minmax_subset_Icc (f : DivFunction) : Ioo (f.xmin_01 : ℝ) f.xmax_01 ⊆ Icc 0 1 := by
  intro x
  simp only [mem_Ioo, mem_Icc, and_imp]
  exact fun h1 h2 ↦ ⟨f.xmin_01.2.1.trans h1.le, h2.le.trans f.xmax_01.2.2⟩

lemma minmaxOrderIso_symm_mem_Icc (f : DivFunction) (x : ℝ) :
    (f.minmaxOrderIso.symm x : ℝ) ∈ Icc (0 : ℝ) 1 :=
  f.Ioo_minmax_subset_Icc (f.minmaxOrderIso.symm x).2

noncomputable
def realToENNRealIoo (f : DivFunction) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.orderIsoUnitIntervalBirational.symm
    (⟨f.minmaxOrderIso.symm x, f.minmaxOrderIso_symm_mem_Icc x⟩ : Icc (0 : ℝ) 1)

lemma realToENNRealIoo_mono (f : DivFunction) {x y : ℝ} (hxy : x ≤ y) :
    f.realToENNRealIoo x ≤ f.realToENNRealIoo y := by
  rw [realToENNRealIoo, realToENNRealIoo]
  refine ENNReal.orderIsoUnitIntervalBirational.symm.monotone ?_
  suffices f.minmaxOrderIso.symm x ≤ f.minmaxOrderIso.symm y from mod_cast this
  exact f.minmaxOrderIso.symm.monotone hxy

@[continuity, fun_prop]
lemma continuous_realToENNRealIoo (f : DivFunction) : Continuous f.realToENNRealIoo := by
  unfold realToENNRealIoo
  refine ENNReal.orderIsoUnitIntervalBirational.symm.continuous.comp ?_
  refine Continuous.subtype_mk ?_ f.minmaxOrderIso_symm_mem_Icc
  refine Continuous.subtype_val ?_
  exact f.minmaxOrderIso.symm.continuous

lemma xmin_lt_realToENNRealIoo (f : DivFunction) (x : ℝ) :
    f.xmin < f.realToENNRealIoo x := by
  rw [realToENNRealIoo, ← orderIsoUnitIntervalBirational_xmin_01, OrderIso.lt_iff_lt]
  suffices (f.xmin_01 : ℝ) < f.minmaxOrderIso.symm x from mod_cast this
  exact (f.minmaxOrderIso.symm x).2.1

lemma realToENNRealIoo_lt_xmax (f : DivFunction) (x : ℝ) :
    f.realToENNRealIoo x < f.xmax := by
  rw [realToENNRealIoo, ← orderIsoUnitIntervalBirational_xmax_01, OrderIso.lt_iff_lt]
  suffices f.minmaxOrderIso.symm x < (f.xmax_01 : ℝ) from mod_cast this
  exact (f.minmaxOrderIso.symm x).2.2

lemma realToENNRealIoo_mem_Ioo (f : DivFunction) (x : ℝ) :
    f.realToENNRealIoo x ∈ Ioo f.xmin f.xmax :=
  ⟨f.xmin_lt_realToENNRealIoo x, f.realToENNRealIoo_lt_xmax x⟩

lemma realToENNRealIoo_ne_top (f : DivFunction) (x : ℝ) :
    f.realToENNRealIoo x ≠ ∞ := ne_top_of_lt (f.realToENNRealIoo_lt_xmax x)

noncomputable
def rightDerivEnlarged (f : DivFunction) (x : ℝ) : ℝ :=
  rightDeriv f.realFun (f.realToENNRealIoo x).toReal

noncomputable
def rightDerivEnlargedStieltjes (f : DivFunction) : StieltjesFunction where
  toFun := f.rightDerivEnlarged
  mono' x y hxy := by
    simp only [rightDerivEnlarged]
    refine f.rightDeriv_mono ?_ ?_ ?_
    · rw [ENNReal.toReal_le_toReal (f.realToENNRealIoo_ne_top _) (f.realToENNRealIoo_ne_top _)]
      exact f.realToENNRealIoo_mono hxy
    · rw [ENNReal.ofReal_toReal (f.realToENNRealIoo_ne_top _)]
      exact f.xmin_lt_realToENNRealIoo x
    · rw [ENNReal.ofReal_toReal (f.realToENNRealIoo_ne_top _)]
      exact f.realToENNRealIoo_lt_xmax y
  right_continuous' x := by
    have h := f.continuousWithinAt_rightDeriv (x := (f.realToENNRealIoo x).toReal) ?_ ?_
    rotate_left
    · rw [ENNReal.ofReal_toReal (f.realToENNRealIoo_ne_top _)]
      exact f.xmin_lt_realToENNRealIoo x
    · rw [ENNReal.ofReal_toReal (f.realToENNRealIoo_ne_top _)]
      exact f.realToENNRealIoo_lt_xmax x
    unfold rightDerivEnlarged
    rw [ContinuousWithinAt] at h ⊢
    refine h.comp ?_
    rw [tendsto_nhdsWithin_iff]
    constructor
    · refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      refine (ENNReal.tendsto_toReal (f.realToENNRealIoo_ne_top _)).comp ?_
      exact f.continuous_realToENNRealIoo.tendsto _
    · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      simp only [mem_Ici]
      rw [ENNReal.toReal_le_toReal (f.realToENNRealIoo_ne_top _) (f.realToENNRealIoo_ne_top _)]
      exact f.realToENNRealIoo_mono hy

noncomputable
def enlargedCurvatureMeasure (f : DivFunction) : Measure ℝ :=
  f.rightDerivEnlargedStieltjes.measure

/-- The curvature measure induced by a convex function. It is defined as the only measure that has
the right derivative of the function as a CDF. -/
noncomputable
irreducible_def curvatureMeasure (f : DivFunction) : Measure ℝ≥0∞ :=
  f.rightDerivStieltjes.measure.map ENNReal.ofReal

lemma curvatureMeasure_Ioi (a : ℝ≥0∞) (ha : a ≠ ∞) :
    f.curvatureMeasure (Ioi a) = f.rightDerivStieltjes.measure (Ioi a.toReal) := by
  rw [curvatureMeasure, Measure.map_apply]
  · congr
    ext x
    simp only [mem_preimage, mem_Ioi]
    rw [ENNReal.lt_ofReal_iff_toReal_lt ha]
  · fun_prop
  · simp

lemma curvatureMeasure_singleton_top : f.curvatureMeasure {∞} = 0 := by
  rw [curvatureMeasure, Measure.map_apply]
  · have : ENNReal.ofReal ⁻¹' {⊤} = ∅ := by ext; simp
    simp [this]
  · exact ENNReal.measurable_ofReal
  · simp

lemma curvatureMeasure_add (hf : ∀ x, 0 < x → f x ≠ ∞) (hg : ∀ x, 0 < x → g x ≠ ∞) :
    curvatureMeasure (f + g) = curvatureMeasure f + curvatureMeasure g := by
  simp_rw [curvatureMeasure, ← Measure.map_add _ _ ENNReal.measurable_ofReal]
  -- that proof does not work for now. Need to generalize `ERealStieltjes.measure_add`
  rw [← ERealStieltjes.measure_add, rightDerivStieltjes_add]
  · exact fun x ↦ ⟨sorry, rightDerivStieltjes_ne_top hf x⟩
  · exact fun x ↦ ⟨sorry, rightDerivStieltjes_ne_top hg x⟩

-- /-- A Taylor formula for convex functions in terms of the right derivative
-- and the curvature measure. -/
-- theorem convex_taylor (hf : ConvexOn ℝ univ f) (hf_cont : Continuous f) {a b : ℝ} :
--     f b - f a - (rightDeriv f a) * (b - a)  = ∫ x in a..b, b - x ∂(curvatureMeasure f) := by
--   have h_int : IntervalIntegrable (rightDeriv f) volume a b := hf.rightDeriv_mono.intervalIntegrable
--   rw [← intervalIntegral.integral_eq_sub_of_hasDeriv_right hf_cont.continuousOn
--     (fun x _ ↦ hf.hadDerivWithinAt_rightDeriv x) h_int]
--   simp_rw [← neg_sub _ b, intervalIntegral.integral_neg, curvatureMeasure_of_convexOn hf,
--     mul_neg, sub_neg_eq_add, mul_comm _ (a - b)]
--   let g := StieltjesFunction.id + StieltjesFunction.const (-b)
--   have hg : g = fun x ↦ x - b := rfl
--   rw [← hg, integral_stieltjes_meas_by_parts g hf.rightDerivStieltjes]
--   swap; · rw [hg]; fun_prop
--   simp only [Real.volume_eq_stieltjes_id, add_apply, id_apply, id_eq, const_apply, add_neg_cancel,
--     zero_mul, zero_sub, measure_add, measure_const, add_zero, neg_sub, sub_neg_eq_add, g]
--   rfl

/-- A Taylor formula for convex functions in terms of the right derivative
and the curvature measure. -/
theorem convex_taylor_one {b : ℝ≥0∞} (hb : 1 ≤ b) :
    f b = ∫⁻ x in (Icc 1 b), b - x ∂f.curvatureMeasure := by
  rw [curvatureMeasure, setLIntegral_map]
  have h_int : IntervalIntegrable f.rightDerivStieltjes volume 1 b :=
      f.rightDerivStieltjes.mono.intervalIntegrable
  rw [← intervalIntegral.integral_eq_sub_of_hasDeriv_right hf_cont.continuousOn
    (fun x _ ↦ hf.hadDerivWithinAt_rightDeriv x) h_int]
  simp_rw [← neg_sub _ b, intervalIntegral.integral_neg, curvatureMeasure_of_convexOn hf,
    mul_neg, sub_neg_eq_add, mul_comm _ (a - b)]
  let g := StieltjesFunction.id + StieltjesFunction.const (-b)
  have hg : g = fun x ↦ x - b := rfl
  rw [← hg, integral_stieltjes_meas_by_parts g hf.rightDerivStieltjes]
  swap; · rw [hg]; fun_prop
  simp only [Real.volume_eq_stieltjes_id, add_apply, id_apply, id_eq, const_apply, add_neg_cancel,
    zero_mul, zero_sub, measure_add, measure_const, add_zero, neg_sub, sub_neg_eq_add, g]
  rfl

end DivFunction

end ProbabilityTheory

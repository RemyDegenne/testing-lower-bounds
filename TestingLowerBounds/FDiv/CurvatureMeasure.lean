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


open MeasureTheory Set StieltjesFunction Function Filter

open scoped ENNReal Topology

namespace ProbabilityTheory

namespace DivFunction

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳} {f g : DivFunction} {β γ x t : ℝ}

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

noncomputable
def realToMinmaxOrderIso (f : DivFunction) : ℝ ≃o Ioo f.xmin f.xmax where
  invFun x := f.minmaxOrderIso ⟨ENNReal.orderIsoUnitIntervalBirational x, by
    constructor
    · norm_cast
      rw [xmin_01, ENNReal.orderIsoUnitIntervalBirational.lt_iff_lt]
      exact x.2.1
    · norm_cast
      rw [xmax_01, ENNReal.orderIsoUnitIntervalBirational.lt_iff_lt]
      exact x.2.2⟩
  toFun x := ⟨f.realToENNRealIoo x, ⟨f.xmin_lt_realToENNRealIoo x, f.realToENNRealIoo_lt_xmax x⟩⟩
  right_inv x := by
    ext
    simp only
    rw [realToENNRealIoo]
    simp only [OrderIso.symm_apply_apply]
    rw [OrderIso.symm_apply_apply]
  left_inv x := by simp [realToENNRealIoo]
  map_rel_iff' {x y} := by
    simp only [realToENNRealIoo, Equiv.coe_fn_mk, OrderIsoClass.map_le_map_iff, Subtype.mk_le_mk]
    norm_cast
    rw [f.minmaxOrderIso.symm.le_iff_le]

lemma realToMinmaxOrderIso_ne_top (f : DivFunction) {x : ℝ} :
    (f.realToMinmaxOrderIso x : ℝ≥0∞) ≠ ∞ := ne_top_of_lt (f.realToENNRealIoo_lt_xmax x)

/-- Map `ℝ` to the interior of the effective domain of `f`, `Ioo f.xmin f.xmax`, then take the
right derivative.
This transformation of the domain from an interval to `ℝ` allows us to get a function from `ℝ`
to `ℝ`, which is needed to define a Stieltjes function and get a measure from it. -/
noncomputable
def rightDerivEnlarged (f : DivFunction) (x : ℝ) : ℝ :=
  rightDeriv f.realFun ((f.realToMinmaxOrderIso x : ℝ≥0∞)).toReal

noncomputable
def rightDerivEnlargedStieltjes (f : DivFunction) : StieltjesFunction where
  toFun := f.rightDerivEnlarged
  mono' x y hxy := by
    simp only [rightDerivEnlarged]
    refine f.rightDeriv_mono ?_ ?_ ?_
    · rw [ENNReal.toReal_le_toReal f.realToMinmaxOrderIso_ne_top f.realToMinmaxOrderIso_ne_top]
      simp [hxy]
    · rw [ENNReal.ofReal_toReal f.realToMinmaxOrderIso_ne_top]
      exact (f.realToMinmaxOrderIso x).2.1
    · rw [ENNReal.ofReal_toReal f.realToMinmaxOrderIso_ne_top]
      exact (f.realToMinmaxOrderIso y).2.2
  right_continuous' x := by
    unfold rightDerivEnlarged
    have h := f.continuousWithinAt_rightDeriv (x := (f.realToMinmaxOrderIso x : ℝ≥0∞).toReal) ?_ ?_
    rotate_left
    · rw [ENNReal.ofReal_toReal f.realToMinmaxOrderIso_ne_top]
      exact (f.realToMinmaxOrderIso x).2.1
    · rw [ENNReal.ofReal_toReal f.realToMinmaxOrderIso_ne_top]
      exact (f.realToMinmaxOrderIso x).2.2
    rw [ContinuousWithinAt] at h ⊢
    refine h.comp ?_
    rw [tendsto_nhdsWithin_iff]
    constructor
    · refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      refine (ENNReal.tendsto_toReal f.realToMinmaxOrderIso_ne_top).comp ?_
      exact f.realToMinmaxOrderIso.continuous.subtype_val.tendsto x
    · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      rw [mem_Ici, ENNReal.toReal_le_toReal f.realToMinmaxOrderIso_ne_top
        f.realToMinmaxOrderIso_ne_top]
      simp [mem_Ici.mp hy]

noncomputable
def enlargedCurvatureMeasure (f : DivFunction) : Measure ℝ :=
  f.rightDerivEnlargedStieltjes.measure

noncomputable
def curvatureMeasure_Ioo (f : DivFunction) : Measure (Ioo f.xmin f.xmax) :=
  f.enlargedCurvatureMeasure.map f.realToMinmaxOrderIso.toHomeomorph.toMeasurableEquiv

open Classical in
/-- The curvature measure induced by a convex function. It is defined as the only measure that has
the right derivative of the function as a CDF. -/
noncomputable
def curvatureMeasure (f : DivFunction) : Measure ℝ≥0∞ :=
  (if Tendsto f.rightDerivEnlarged atBot atBot then 0 else ∞) • Measure.dirac f.xmin
  + f.curvatureMeasure_Ioo.map (Subtype.val : Ioo f.xmin f.xmax → ℝ≥0∞)
  + (if Tendsto f.rightDerivEnlarged atTop atTop then 0 else ∞) • Measure.dirac f.xmax

lemma curvatureMeasure_add (f g : DivFunction) :
    (f + g).curvatureMeasure = f.curvatureMeasure + g.curvatureMeasure := by
  sorry

theorem convex_taylor_one_right {b : ℝ≥0∞} (hb : 1 ≤ b) :
    f b = ∫⁻ x in Icc 1 b, b - x ∂f.curvatureMeasure := by
  sorry

theorem convex_taylor_one_left {b : ℝ≥0∞} (hb : b ≤ 1) :
    f b = ∫⁻ x in Icc b 1, x - b ∂f.curvatureMeasure := by
  sorry

-- /-- The curvature measure induced by a convex function. It is defined as the only measure that has
-- the right derivative of the function as a CDF. -/
-- noncomputable
-- irreducible_def curvatureMeasure (f : DivFunction) : Measure ℝ≥0∞ :=
--   f.rightDerivStieltjes.measure.map ENNReal.ofReal

-- lemma curvatureMeasure_Ioi (a : ℝ≥0∞) (ha : a ≠ ∞) :
--     f.curvatureMeasure (Ioi a) = f.rightDerivStieltjes.measure (Ioi a.toReal) := by
--   rw [curvatureMeasure, Measure.map_apply]
--   · congr
--     ext x
--     simp only [mem_preimage, mem_Ioi]
--     rw [ENNReal.lt_ofReal_iff_toReal_lt ha]
--   · fun_prop
--   · simp

-- lemma curvatureMeasure_singleton_top : f.curvatureMeasure {∞} = 0 := by
--   rw [curvatureMeasure, Measure.map_apply]
--   · have : ENNReal.ofReal ⁻¹' {⊤} = ∅ := by ext; simp
--     simp [this]
--   · exact ENNReal.measurable_ofReal
--   · simp

-- lemma curvatureMeasure_add (hf : ∀ x, 0 < x → f x ≠ ∞) (hg : ∀ x, 0 < x → g x ≠ ∞) :
--     curvatureMeasure (f + g) = curvatureMeasure f + curvatureMeasure g := by
--   simp_rw [curvatureMeasure, ← Measure.map_add _ _ ENNReal.measurable_ofReal]
--   -- that proof does not work for now. Need to generalize `ERealStieltjes.measure_add`
--   rw [← ERealStieltjes.measure_add, rightDerivStieltjes_add]
--   · exact fun x ↦ ⟨sorry, rightDerivStieltjes_ne_top hf x⟩
--   · exact fun x ↦ ⟨sorry, rightDerivStieltjes_ne_top hg x⟩

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

end DivFunction

end ProbabilityTheory

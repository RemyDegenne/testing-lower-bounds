/-
Copyright (c) 2024 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TestingLowerBounds.Sorry.ByParts
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import TestingLowerBounds.FDiv.DivFunction.RightDeriv


open MeasureTheory Set StieltjesFunction Function Filter

open scoped ENNReal Topology

namespace ProbabilityTheory

lemma ENNReal.preimage_toReal_Ioc {a b : ℝ} (h : 0 ≤ a) :
    ENNReal.toReal ⁻¹' Ioc a b = Ioc (ENNReal.ofReal a) (ENNReal.ofReal b) := by
  ext x
  rcases lt_or_ge b a with hb | hb
  · rw [Ioc_eq_empty (not_lt.mpr hb.le), Ioc_eq_empty]
    · simp
    · rw [not_lt, ENNReal.ofReal_le_ofReal_iff h]
      exact hb.le
  simp only [mem_preimage, mem_Ioc]
  by_cases hx_top : x = ∞
  · simp [hx_top, not_lt.mpr h]
  rw [ENNReal.le_ofReal_iff_toReal_le hx_top (h.trans hb),
    ENNReal.ofReal_lt_iff_lt_toReal h hx_top]

namespace DivFunction

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {μ ν : Measure 𝒳} {f g : DivFunction} {β γ x t : ℝ}

-- theorem orderIsoUnitIntervalBirational_symm_apply (x : Icc 0 1) :
--     ENNReal.orderIsoUnitIntervalBirational.symm x
--       = if x = 0 then 0 else if x = 1 then ∞ else ENNReal.ofReal ((x : ℝ)⁻¹ - 1)⁻¹ := by
--   suffices x = ENNReal.orderIsoUnitIntervalBirational
--       (if x = 0 then 0 else if x = 1 then ∞ else ENNReal.ofReal ((x : ℝ)⁻¹ - 1)⁻¹) by
--     conv_lhs => rw [this, OrderIso.symm_apply_apply]
--   ext
--   simp only [ENNReal.orderIsoUnitIntervalBirational_apply_coe, ENNReal.toReal_inv]
--   by_cases hx0 : x = 0
--   · simp [hx0]
--   by_cases hx1 : x = 1
--   · simp [hx1]
--   rw [ite_eq_right hx0, ite_eq_right hx1]
--   have hx_ne0 : (x : ℝ) ≠ 0 := fun h ↦ hx0 (by ext; simp only [Icc.coe_zero, Icc.coe_eq_zero, h])
--   have hx_ne1 : (x : ℝ) ≠ 1 := fun h ↦ hx1 (by ext; simp only [Icc.coe_one, Icc.coe_eq_one, h])
--   rw [ENNReal.toReal_add, ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_ofReal]
--   · simp
--   · simp only [inv_nonneg, sub_nonneg]
--     rw [one_le_inv₀ (lt_of_le_of_ne x.2.1 hx_ne0.symm)]
--     exact x.2.2
--   · simp only [ne_eq, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero, inv_nonpos, tsub_le_iff_right,
--       zero_add, not_le]
--     rw [one_lt_inv₀ (lt_of_le_of_ne x.2.1 hx_ne0.symm)]
--     exact lt_of_le_of_ne x.2.2 hx_ne1
--   · simp

-- noncomputable
-- def xmin_01 (f : DivFunction) : Icc (0 : ℝ) 1 := ENNReal.orderIsoUnitIntervalBirational f.xmin

-- lemma coe_xmin_01 : (f.xmin_01 : ℝ) = (f.xmin⁻¹ + 1).toReal⁻¹ := by simp [xmin_01]

-- lemma orderIsoUnitIntervalBirational_xmin_01 (f : DivFunction) :
--     ENNReal.orderIsoUnitIntervalBirational.symm f.xmin_01 = f.xmin := by
--   simp [xmin_01]

-- noncomputable
-- def xmax_01 (f : DivFunction) : Icc (0 : ℝ) 1 := ENNReal.orderIsoUnitIntervalBirational f.xmax

-- lemma coe_xmax_01 : (f.xmax_01 : ℝ) = (f.xmax.toReal⁻¹ + 1)⁻¹ := by
--   simp only [xmax_01, ENNReal.orderIsoUnitIntervalBirational_apply_coe, ENNReal.toReal_inv, inv_inj]
--   rw [ENNReal.toReal_add, ENNReal.toReal_inv]
--   · simp
--   · simp [xmax_pos.ne']
--   · simp

-- lemma orderIsoUnitIntervalBirational_xmax_01 (f : DivFunction) :
--     ENNReal.orderIsoUnitIntervalBirational.symm f.xmax_01 = f.xmax := by
--   simp [xmax_01]

-- lemma xmin_01_lt_xmax_01 : (f.xmin_01 : ℝ) < f.xmax_01 := sorry

-- noncomputable
-- def minmaxOrderIso (f : DivFunction) : Ioo (f.xmin_01 : ℝ) f.xmax_01 ≃o ℝ :=
--   (IooOrderIsoIoo (ENNReal.orderIsoUnitIntervalBirational.lt_iff_lt.mpr xmin_lt_xmax)).trans
--     IooOrderIsoReal

-- @[simp]
-- lemma minmaxOrderIso_apply (x : Ioo (f.xmin_01 : ℝ) f.xmax_01) :
--     f.minmaxOrderIso x
--       = Real.log ((x - f.xmin_01) / (f.xmax_01 - x)) := by
--   simp only [minmaxOrderIso, ENNReal.orderIsoUnitIntervalBirational_apply_coe, OrderIso.trans_apply,
--     IooOrderIsoReal_apply]
--   rw [IooOrderIsoIoo_apply_coe (hab := xmin_01_lt_xmax_01)]
--   congr 1
--   rw [one_sub_div, sub_sub_sub_cancel_right, div_div_div_cancel_right₀]
--   · rw [sub_ne_zero]
--     exact xmin_01_lt_xmax_01.ne'
--   · rw [sub_ne_zero]
--     exact xmin_01_lt_xmax_01.ne'

-- lemma div_xmin_xmax_exp_mem_Ioo (x : ℝ) :
--     (f.xmin_01 + f.xmax_01 * Real.exp x) / (1 + Real.exp x)
--       ∈ Ioo (f.xmin_01 : ℝ) f.xmax_01 := by
--   simp only [mem_Ioo]
--   constructor
--   · sorry
--   · sorry

-- @[simp]
-- lemma minmaxOrderIso_symm_apply_coe (x : ℝ) :
--     (f.minmaxOrderIso.symm x : ℝ) = (f.xmin_01 + f.xmax_01 * Real.exp x) / (1 + Real.exp x) := by
--   have h_mem : (f.xmin_01 + f.xmax_01 * Real.exp x) / (1 + Real.exp x)
--       ∈ Ioo (f.xmin_01 : ℝ) f.xmax_01 := div_xmin_xmax_exp_mem_Ioo _
--   suffices x = f.minmaxOrderIso ⟨(f.xmin_01 + f.xmax_01 * Real.exp x) / (1 + Real.exp x), h_mem⟩ by
--     conv_lhs => rw [this, OrderIso.symm_apply_apply]
--   simp only [minmaxOrderIso_apply]
--   have h1 : f.xmax_01 + f.xmax_01 * Real.exp x - (f.xmin_01 + f.xmax_01 * Real.exp x)
--       = f.xmax_01 - f.xmin_01 := by ring
--   have h2 : f.xmin_01 + f.xmax_01 * Real.exp x - (f.xmin_01 + Real.exp x * f.xmin_01)
--       = (f.xmax_01 - f.xmin_01) * Real.exp x := by ring
--   rw [sub_div', mul_add, mul_one, h1, div_sub', add_mul, one_mul, h2, div_div_div_cancel_right₀,
--     mul_div_assoc, mul_div_cancel₀, Real.log_exp]
--   · rw [sub_ne_zero]
--     exact xmin_01_lt_xmax_01.ne'
--   · positivity
--   · positivity
--   · positivity

-- lemma Ioo_minmax_subset_Icc (f : DivFunction) : Ioo (f.xmin_01 : ℝ) f.xmax_01 ⊆ Icc 0 1 := by
--   intro x
--   simp only [mem_Ioo, mem_Icc, and_imp]
--   exact fun h1 h2 ↦ ⟨f.xmin_01.2.1.trans h1.le, h2.le.trans f.xmax_01.2.2⟩

-- lemma minmaxOrderIso_symm_mem_Icc (f : DivFunction) (x : ℝ) :
--     (f.minmaxOrderIso.symm x : ℝ) ∈ Icc (0 : ℝ) 1 :=
--   f.Ioo_minmax_subset_Icc (f.minmaxOrderIso.symm x).2

-- noncomputable
-- def realToENNRealIoo (f : DivFunction) (x : ℝ) : ℝ≥0∞ :=
--   ENNReal.orderIsoUnitIntervalBirational.symm
--     (⟨f.minmaxOrderIso.symm x, f.minmaxOrderIso_symm_mem_Icc x⟩ : Icc (0 : ℝ) 1)

-- lemma xmin_lt_realToENNRealIoo (f : DivFunction) (x : ℝ) :
--     f.xmin < f.realToENNRealIoo x := by
--   rw [realToENNRealIoo, ← orderIsoUnitIntervalBirational_xmin_01, OrderIso.lt_iff_lt]
--   suffices (f.xmin_01 : ℝ) < f.minmaxOrderIso.symm x from mod_cast this
--   exact (f.minmaxOrderIso.symm x).2.1

-- lemma realToENNRealIoo_lt_xmax (f : DivFunction) (x : ℝ) :
--     f.realToENNRealIoo x < f.xmax := by
--   rw [realToENNRealIoo, ← orderIsoUnitIntervalBirational_xmax_01, OrderIso.lt_iff_lt]
--   suffices f.minmaxOrderIso.symm x < (f.xmax_01 : ℝ) from mod_cast this
--   exact (f.minmaxOrderIso.symm x).2.2

-- noncomputable
-- def realToMinmaxOrderIso (f : DivFunction) : ℝ ≃o Ioo f.xmin f.xmax where
--   invFun x := f.minmaxOrderIso ⟨ENNReal.orderIsoUnitIntervalBirational x, by
--     constructor
--     · norm_cast
--       rw [xmin_01, ENNReal.orderIsoUnitIntervalBirational.lt_iff_lt]
--       exact x.2.1
--     · norm_cast
--       rw [xmax_01, ENNReal.orderIsoUnitIntervalBirational.lt_iff_lt]
--       exact x.2.2⟩
--   toFun x := ⟨f.realToENNRealIoo x, ⟨f.xmin_lt_realToENNRealIoo x, f.realToENNRealIoo_lt_xmax x⟩⟩
--   right_inv x := by
--     ext
--     simp only
--     rw [realToENNRealIoo]
--     simp only [OrderIso.symm_apply_apply]
--     rw [OrderIso.symm_apply_apply]
--   left_inv x := by simp only [realToENNRealIoo, OrderIso.apply_symm_apply, Subtype.coe_eta]
--   map_rel_iff' {x y} := by
--     simp only [realToENNRealIoo, Equiv.coe_fn_mk, OrderIsoClass.map_le_map_iff, Subtype.mk_le_mk]
--     norm_cast
--     rw [f.minmaxOrderIso.symm.le_iff_le]

-- lemma realToMinMaxOrderIso_apply_coe (f : DivFunction) (x : ℝ) :
--     (f.realToMinmaxOrderIso x : ℝ≥0∞)
--       = ENNReal.ofReal ((f.xmin_01 + f.xmax_01 * Real.exp x)
--                           / (1 - f.xmin_01 + (1 - f.xmax_01) * Real.exp x)) := by
--   simp only [realToMinmaxOrderIso, realToENNRealIoo, minmaxOrderIso_symm_apply_coe,
--     ENNReal.orderIsoUnitIntervalBirational_apply_coe, ENNReal.toReal_inv, minmaxOrderIso_apply,
--     RelIso.coe_fn_mk, Equiv.coe_fn_mk]
--   rw [orderIsoUnitIntervalBirational_symm_apply]
--   simp only [inv_div]
--   have h := div_xmin_xmax_exp_mem_Ioo (f := f) (x := x)
--   rw [ite_eq_right, ite_eq_right]
--   rotate_left
--   · rw [Subtype.ext_iff]
--     simp only [Icc.coe_one]
--     exact (h.2.trans_le f.xmax_01.2.2).ne
--   · rw [Subtype.ext_iff]
--     simp only [Icc.coe_zero]
--     refine (ne_of_lt ?_).symm
--     exact f.xmin_01.2.1.trans_lt h.1
--   rw [div_sub_one, inv_div]
--   · congr
--     ring
--   · refine (ne_of_lt ?_).symm
--     refine add_pos_of_nonneg_of_pos f.xmin_01.2.1 ((mul_pos_iff_of_pos_right ?_).mpr ?_)
--     · positivity
--     · exact f.xmin_01.2.1.trans_lt xmin_01_lt_xmax_01

-- lemma realToMinmaxOrderIso_ne_top (f : DivFunction) {x : ℝ} :
--     (f.realToMinmaxOrderIso x : ℝ≥0∞) ≠ ∞ := by simp [realToMinMaxOrderIso_apply_coe]

-- lemma toReal_realToMinMaxOrderIso_apply (f : DivFunction) (x : ℝ) :
--     (f.realToMinmaxOrderIso x : ℝ≥0∞).toReal
--       = (f.xmin_01 + f.xmax_01 * Real.exp x) / (1 - f.xmin_01 + (1 - f.xmax_01) * Real.exp x) := by
--   simp only [realToMinMaxOrderIso_apply_coe, ENNReal.toReal_ofReal_eq_iff]
--   refine div_nonneg ?_ ?_
--   · exact add_nonneg f.xmin_01.2.1 (mul_nonneg f.xmax_01.2.1 (by positivity))
--   · refine add_nonneg ?_ (mul_nonneg ?_ (by positivity))
--     · simp [f.xmin_01.2.2]
--     · simp [f.xmax_01.2.2]

-- lemma measurableEmbedding_toReal_realToMinMaxOrderIso :
--     MeasurableEmbedding (fun x ↦ (f.realToMinmaxOrderIso x : ℝ≥0∞).toReal) := by
--   have h1 := f.realToMinmaxOrderIso.toHomeomorph.toMeasurableEquiv.measurableEmbedding
--   change MeasurableEmbedding ((ENNReal.toReal ∘ Subtype.val) ∘ f.realToMinmaxOrderIso)
--   refine MeasurableEmbedding.comp ?_ h1
--   sorry

-- lemma hasDerivAt_toReal_realToMinMaxOrderIso (f : DivFunction) (x : ℝ) :
--     HasDerivAt (fun x ↦ (f.realToMinmaxOrderIso x : ℝ≥0∞).toReal)
--       (Real.exp x * (f.xmax_01 - f.xmin_01) / (1 - f.xmin_01 + (1 - f.xmax_01) * Real.exp x)^2)
--       x := by
--   sorry

-- lemma hasDerivAt_toReal_realToMinMaxOrderIso2 (f : DivFunction) (x : ℝ) :
--     HasDerivAt
--       (fun x ↦ Real.exp x * (f.xmax_01 - f.xmin_01) / (1 - f.xmin_01 + (1 - f.xmax_01) * Real.exp x)^2)
--       ((f.xmax_01 - f.xmin_01) * Real.exp x *
--         ((1 - f.xmin_01)^2 - ((1 - f.xmax_01) * Real.exp x)^2)
--         / (1 - f.xmin_01 + (1 - f.xmax_01) * Real.exp x)^4)
--       x := by
--   sorry

-- lemma strictMono_toReal_realToMinMaxOrderIso (f : DivFunction):
--     StrictMono fun x ↦ (f.realToMinmaxOrderIso x : ℝ≥0∞).toReal := by
--   sorry

-- /-- Map `ℝ` to the interior of the effective domain of `f`, `Ioo f.xmin f.xmax`, then take the
-- right derivative.
-- This transformation of the domain from an interval to `ℝ` allows us to get a function from `ℝ`
-- to `ℝ`, which is needed to define a Stieltjes function and get a measure from it. -/
-- noncomputable
-- def rightDerivEnlarged (f : DivFunction) (x : ℝ) : ℝ :=
--   rightDeriv f.realFun (f.realToMinmaxOrderIso x : ℝ≥0∞).toReal

-- lemma rightDeriv_comp {f g : ℝ → ℝ}
--     (hf_diff : DifferentiableWithinAt ℝ f (Ioi (g x)) (g x))
--     (hg_diff : DifferentiableWithinAt ℝ g (Ioi x) x) (hg : StrictMono g) :
--     rightDeriv (f ∘ g) x = rightDeriv f (g x) * rightDeriv g x := by
--   simp_rw [rightDeriv]
--   rw [derivWithin.comp]
--   · exact hf_diff
--   · exact hg_diff
--   · exact hg.mapsTo_Ioi
--   · exact uniqueDiffWithinAt_Ioi x

-- noncomputable
-- def rightDerivEnlargedStieltjes (f : DivFunction) : StieltjesFunction where
--   toFun := f.rightDerivEnlarged
--   mono' x y hxy := by
--     simp only [rightDerivEnlarged]
--     --rw [rightDeriv_comp, rightDeriv_comp]
--     -- rotate_left
--     -- · sorry
--     -- · exact (f.hasDerivAt_toReal_realToMinMaxOrderIso y).differentiableAt.differentiableWithinAt
--     -- · exact f.strictMono_toReal_realToMinMaxOrderIso
--     -- · sorry
--     -- · exact (f.hasDerivAt_toReal_realToMinMaxOrderIso x).differentiableAt.differentiableWithinAt
--     -- · exact f.strictMono_toReal_realToMinMaxOrderIso
--     -- refine mul_le_mul_of_nonneg' ?_ ?_ ?_ ?_
--     refine f.rightDeriv_mono ?_ ?_ ?_
--     rw [ENNReal.toReal_le_toReal f.realToMinmaxOrderIso_ne_top f.realToMinmaxOrderIso_ne_top]
--     simp only [Subtype.coe_le_coe, OrderIsoClass.map_le_map_iff, hxy]
--     · rw [ENNReal.ofReal_toReal f.realToMinmaxOrderIso_ne_top]
--       exact (f.realToMinmaxOrderIso x).2.1
--     · rw [ENNReal.ofReal_toReal f.realToMinmaxOrderIso_ne_top]
--       exact (f.realToMinmaxOrderIso y).2.2
--     -- · sorry
--     -- · sorry
--     -- · sorry
--   right_continuous' x := by
--     unfold rightDerivEnlarged
--     have h := f.continuousWithinAt_rightDeriv (x := (f.realToMinmaxOrderIso x : ℝ≥0∞).toReal) ?_ ?_
--     rotate_left
--     · rw [ENNReal.ofReal_toReal f.realToMinmaxOrderIso_ne_top]
--       exact (f.realToMinmaxOrderIso x).2.1
--     · rw [ENNReal.ofReal_toReal f.realToMinmaxOrderIso_ne_top]
--       exact (f.realToMinmaxOrderIso x).2.2
--     rw [ContinuousWithinAt] at h ⊢
--     refine h.comp ?_
--     rw [tendsto_nhdsWithin_iff]
--     constructor
--     · refine tendsto_nhdsWithin_of_tendsto_nhds ?_
--       refine (ENNReal.tendsto_toReal f.realToMinmaxOrderIso_ne_top).comp ?_
--       exact f.realToMinmaxOrderIso.continuous.subtype_val.tendsto x
--     · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
--       rw [mem_Ici, ENNReal.toReal_le_toReal f.realToMinmaxOrderIso_ne_top
--         f.realToMinmaxOrderIso_ne_top]
--       simp [mem_Ici.mp hy]

-- noncomputable
-- def enlargedCurvatureMeasure (f : DivFunction) : Measure ℝ :=
--   f.rightDerivEnlargedStieltjes.measure

-- noncomputable
-- def curvatureMeasure_Ioo (f : DivFunction) : Measure (Ioo f.xmin f.xmax) :=
--   f.enlargedCurvatureMeasure.map f.realToMinmaxOrderIso.toHomeomorph.toMeasurableEquiv

-- open Classical in
-- /-- The curvature measure induced by a convex function. It is defined as the only measure that has
-- the right derivative of the function as a CDF. -/
-- noncomputable
-- def curvatureMeasure (f : DivFunction) : Measure ℝ≥0∞ :=
--   (if Tendsto f.rightDerivEnlarged atBot atBot then 0 else ∞) • Measure.dirac f.xmin
--   + f.curvatureMeasure_Ioo.map (Subtype.val : Ioo f.xmin f.xmax → ℝ≥0∞)
--   + (if Tendsto f.rightDerivEnlarged atTop atTop then 0 else ∞) • Measure.dirac f.xmax

-- lemma curvatureMeasure_add (f g : DivFunction) :
--     (f + g).curvatureMeasure = f.curvatureMeasure + g.curvatureMeasure := by
--   sorry

-- lemma todo1 (a b : ℝ) :
--     ∫ x in a..b, x - b ∂f.enlargedCurvatureMeasure
--       = - (a - b) * f.rightDerivEnlargedStieltjes a
--         - ∫ x in a..b, f.rightDerivEnlargedStieltjes x := by
--   let g := StieltjesFunction.id + StieltjesFunction.const (-b)
--   have hg_eq : g = fun x ↦ x - b := rfl
--   have hg_cont : ContinuousOn g (Icc a b) := by rw [hg_eq]; fun_prop
--   change ∫ x in a..b, g x ∂f.enlargedCurvatureMeasure = _
--   unfold enlargedCurvatureMeasure
--   rw [integral_stieltjes_meas_by_parts g f.rightDerivEnlargedStieltjes a b hg_cont]
--   simp only [hg_eq, sub_self, zero_mul, zero_sub, neg_sub]
--   rw [← neg_mul, neg_sub]
--   congr
--   unfold g
--   simp only [measure_add, measure_const, add_zero, Real.volume_eq_stieltjes_id]

-- lemma todo2 (a b : ℝ) :
--     ∫ x in a..b, b - x ∂f.enlargedCurvatureMeasure
--       = (a - b) * f.rightDerivEnlargedStieltjes a
--         + ∫ x in a..b, f.rightDerivEnlargedStieltjes x := by
--   have : ∫ x in a..b, b - x ∂f.enlargedCurvatureMeasure
--       = - ∫ x in a..b, x - b ∂f.enlargedCurvatureMeasure := by
--     unfold intervalIntegral
--     conv_rhs => rw [sub_eq_add_neg, neg_add, ← integral_neg, ← integral_neg]
--     simp_rw [neg_sub, ← sub_eq_add_neg]
--   rw [this, todo1 a b]
--   ring

-- lemma preimage_toReal_realToMinMaxOrderIso_Ioc {a b : ℝ}
--     (ha : ENNReal.ofReal a ∈ Ioo f.xmin f.xmax) (hb : ENNReal.ofReal b ∈ Ioo f.xmin f.xmax) :
--     (fun x ↦ (f.realToMinmaxOrderIso x : ℝ≥0∞).toReal) ⁻¹' Ioc a b
--       = Ioc (f.realToMinmaxOrderIso.symm ⟨ENNReal.ofReal a, ha⟩)
--         (f.realToMinmaxOrderIso.symm ⟨ENNReal.ofReal b, hb⟩) := by
--   sorry

-- lemma image_toReal_realToMinMaxOrderIso_Ioc (a b : ℝ) :
--     (fun x ↦ (f.realToMinmaxOrderIso x : ℝ≥0∞).toReal) '' Ioc a b
--       = Ioc (f.realToMinmaxOrderIso a : ℝ≥0∞).toReal
--         (f.realToMinmaxOrderIso b : ℝ≥0∞).toReal := by
--   sorry

-- -- not what we need
-- lemma todo3 {a b : ℝ}
--     (ha : ENNReal.ofReal a ∈ Ioo f.xmin f.xmax) (hb : ENNReal.ofReal b ∈ Ioo f.xmin f.xmax) :
--     ∫ x in a..b, f.rightDerivEnlargedStieltjes x
--       = ∫ x in ((f.realToMinmaxOrderIso a : ℝ≥0∞).toReal)..((f.realToMinmaxOrderIso b : ℝ≥0∞).toReal),
--         rightDeriv f.realFun x ∂(volume.map (fun x ↦ (f.realToMinmaxOrderIso x : ℝ≥0∞).toReal)) := by
--   simp_rw [intervalIntegral]
--   have h1 := (measurableEmbedding_toReal_realToMinMaxOrderIso (f := f)).setIntegral_map
--     (g := rightDeriv f.realFun) (μ := volume)
--     (s := (fun x ↦ (f.realToMinmaxOrderIso x : ℝ≥0∞).toReal) '' Ioc a b)
--   have h2 := (measurableEmbedding_toReal_realToMinMaxOrderIso (f := f)).setIntegral_map
--     (g := rightDeriv f.realFun) (μ := volume)
--     (s := (fun x ↦ (f.realToMinmaxOrderIso x : ℝ≥0∞).toReal) '' Ioc b a)
--   rw [preimage_image_eq] at h1 h2
--   unfold rightDerivEnlargedStieltjes rightDerivEnlarged
--   simp only
--   rotate_left
--   · sorry
--   · sorry
--   rw [← h1, ← h2, image_toReal_realToMinMaxOrderIso_Ioc, image_toReal_realToMinMaxOrderIso_Ioc]


/-- The curvature measure induced by a convex function. It is defined as the only measure that has
the right derivative of the function as a CDF. -/
noncomputable
irreducible_def curvatureMeasure (f : DivFunction) : Measure ℝ≥0∞ :=
  f.rightDerivStieltjes.measure.map ENNReal.ofReal

lemma curvatureMeasure_Ioi (a : ℝ≥0∞) (ha : a ≠ ∞) :
    f.curvatureMeasure (Ioi a) = f.rightDerivStieltjes.measure (Ioi a.toReal) := by
  rw [curvatureMeasure, Measure.map_apply]
  · congr 1
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

@[simp]
lemma curvatureMeasure_Ioo_top_eq_curvatureMeasure_Ioi {a : ℝ≥0∞} (ha : a ≠ ∞) :
    f.curvatureMeasure (Ioo a ∞) = f.curvatureMeasure (Ioi a) := by
  have : Ioi a = Ioo a ∞ ∪ {∞} := by
    ext x
    simp only [mem_Ioi, union_singleton, mem_insert_iff, mem_Ioo]
    by_cases hx : x = ∞
    · simp [hx, ha.lt_top]
    · simp [Ne.lt_top hx, hx]
  rw [this, measure_union _ (measurableSet_singleton _), curvatureMeasure_singleton_top, add_zero]
  simp

lemma curvatureMeasure_add (hf : ∀ x, 0 < x → f x ≠ ∞) (hg : ∀ x, 0 < x → g x ≠ ∞) :
    curvatureMeasure (f + g) = curvatureMeasure f + curvatureMeasure g := by
  simp_rw [curvatureMeasure, ← Measure.map_add _ _ ENNReal.measurable_ofReal]
  -- that proof does not work for now. Need to generalize `ERealStieltjes.measure_add`
  rw [← ERealStieltjes.measure_add, rightDerivStieltjes_add]
  · exact fun x ↦ ⟨sorry, rightDerivStieltjes_ne_top hf x⟩
  · exact fun x ↦ ⟨sorry, rightDerivStieltjes_ne_top hg x⟩

section ConvexTaylor

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


/-! ### Taylor formula at `1` for a `DivFunction`

We prove `f b = c * (b - 1) + ∫⁻ x in Ioc 1 b, (b - x) ∂f.curvatureMeasure` for `1 ≤ b` and
`f b + c * (1 - b) = ∫⁻ x in Ioc b 1, (x - b) ∂f.curvatureMeasure` for `b ≤ 1`, where
`c = rightDeriv f.realFun 1`. In the interior of the effective domain this is the fundamental
theorem of calculus for the (monotone) right derivative of `f.realFun`, followed by Tonelli's
theorem. The formulas extend to the boundary of the effective domain by monotonicity and
monotone convergence. -/

lemma measure_Ioc_one_right {s : ℝ} (hs : 1 < s) (hs' : ENNReal.ofReal s < f.xmax) :
    f.rightDerivStieltjes.measure (Ioc 1 s)
      = ENNReal.ofReal (rightDeriv f.realFun s - rightDeriv f.realFun 1) := by
  rw [ERealStieltjes.measure_Ioc, rightDerivStieltjes_one,
    rightDerivStieltjes_of_mem_interior (xmin_lt_one.trans (ENNReal.one_lt_ofReal.mpr hs)) hs',
    ← EReal.coe_sub, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma measure_Ioc_one_left {s : ℝ} (hs : f.xmin < ENNReal.ofReal s) (hs' : s ≤ 1) :
    f.rightDerivStieltjes.measure (Ioc s 1)
      = ENNReal.ofReal (rightDeriv f.realFun 1 - rightDeriv f.realFun s) := by
  rw [ERealStieltjes.measure_Ioc, rightDerivStieltjes_one,
    rightDerivStieltjes_of_mem_interior hs ((ENNReal.ofReal_le_one.mpr hs').trans_lt one_lt_xmax),
    ← EReal.coe_sub, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma monotoneOn_rightDeriv_realFun_Icc {a b : ℝ} (ha : f.xmin < ENNReal.ofReal a)
    (hb : ENNReal.ofReal b < f.xmax) :
    MonotoneOn (rightDeriv f.realFun) (Icc a b) := fun _ hx _ hy hxy ↦
  f.rightDeriv_mono hxy (ha.trans_le (ENNReal.ofReal_le_ofReal hx.1))
    ((ENNReal.ofReal_le_ofReal hy.2).trans_lt hb)

lemma continuousOn_realFun_Icc {a b : ℝ} (ha : f.xmin < ENNReal.ofReal a)
    (hb : ENNReal.ofReal b < f.xmax) :
    ContinuousOn f.realFun (Icc a b) :=
  f.continuousOn_realFun_Ioo.mono fun _ hx ↦ mem_toReal_Ioo_iff.mpr
    ⟨ha.trans_le (ENNReal.ofReal_le_ofReal hx.1), (ENNReal.ofReal_le_ofReal hx.2).trans_lt hb⟩

lemma hasDerivWithinAt_realFun {x : ℝ} (hx : f.xmin < ENNReal.ofReal x)
    (hx' : ENNReal.ofReal x < f.xmax) :
    HasDerivWithinAt f.realFun (rightDeriv f.realFun x) (Ioi x) x := by
  have hx0 : 0 ≤ x := by
    by_contra h
    rw [ENNReal.ofReal_of_nonpos (not_le.mp h).le] at hx
    exact ENNReal.not_lt_zero hx
  exact (f.differentiableWithinAt hx0 ⟨hx, hx'⟩).hasDerivWithinAt

lemma intervalIntegrable_rightDeriv_realFun {a b : ℝ} (hab : a ≤ b)
    (ha : f.xmin < ENNReal.ofReal a) (hb : ENNReal.ofReal b < f.xmax) :
    IntervalIntegrable (rightDeriv f.realFun) volume a b := by
  refine MonotoneOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  exact f.monotoneOn_rightDeriv_realFun_Icc ha hb

/-- Fundamental theorem of calculus for `f.realFun` on an interval inside the effective domain. -/
lemma integral_rightDeriv_realFun {a b : ℝ} (hab : a ≤ b) (ha : f.xmin < ENNReal.ofReal a)
    (hb : ENNReal.ofReal b < f.xmax) :
    ∫ s in a..b, rightDeriv f.realFun s = f.realFun b - f.realFun a := by
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right ?_ ?_
    (f.intervalIntegrable_rightDeriv_realFun hab ha hb)
  · rw [uIcc_of_le hab]
    exact f.continuousOn_realFun_Icc ha hb
  · intro x hx
    rw [min_eq_left hab, max_eq_right hab] at hx
    exact f.hasDerivWithinAt_realFun (ha.trans_le (ENNReal.ofReal_le_ofReal hx.1.le))
      ((ENNReal.ofReal_le_ofReal hx.2.le).trans_lt hb)

lemma integral_rightDeriv_realFun_sub_one {t : ℝ} (ht : 1 ≤ t)
    (ht' : ENNReal.ofReal t < f.xmax) :
    ∫ s in (1)..t, (rightDeriv f.realFun s - rightDeriv f.realFun 1)
      = f.realFun t - rightDeriv f.realFun 1 * (t - 1) := by
  rw [intervalIntegral.integral_sub
    (f.intervalIntegrable_rightDeriv_realFun ht (by simpa using xmin_lt_one) ht')
    intervalIntegrable_const,
    f.integral_rightDeriv_realFun ht (by simpa using xmin_lt_one) ht',
    intervalIntegral.integral_const, realFun_one, smul_eq_mul]
  ring

lemma integral_one_sub_rightDeriv_realFun {t : ℝ} (ht : f.xmin < ENNReal.ofReal t)
    (ht' : t ≤ 1) :
    ∫ s in t..(1), (rightDeriv f.realFun 1 - rightDeriv f.realFun s)
      = f.realFun t + rightDeriv f.realFun 1 * (1 - t) := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (f.intervalIntegrable_rightDeriv_realFun ht' ht (by simpa using one_lt_xmax)),
    f.integral_rightDeriv_realFun ht' ht (by simpa using one_lt_xmax),
    intervalIntegral.integral_const, realFun_one, smul_eq_mul]
  ring

/-- Tonelli: `∫⁻ x in Ioc 1 t, (t - x) ∂μ = ∫⁻ s in Ioc 1 t, μ (Ioc 1 s)`. -/
lemma setLIntegral_Ioc_sub_right {t : ℝ} (ht : 1 ≤ t) (ht' : ENNReal.ofReal t < f.xmax) :
    ∫⁻ x in Ioc 1 t, ENNReal.ofReal (t - x) ∂f.rightDerivStieltjes.measure
      = ∫⁻ s in Ioc 1 t, f.rightDerivStieltjes.measure (Ioc 1 s) := by
  set μ := f.rightDerivStieltjes.measure with hμ_def
  have hμ : IsFiniteMeasure (μ.restrict (Ioc 1 t)) := by
    rw [isFiniteMeasure_restrict, hμ_def, ERealStieltjes.measure_Ioc, rightDerivStieltjes_one,
      rightDerivStieltjes_of_mem_interior (xmin_lt_one.trans_le (ENNReal.one_le_ofReal.mpr ht)) ht',
      ← EReal.coe_sub, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _)]
    exact ENNReal.ofReal_ne_top
  let g : ℝ → ℝ → ℝ≥0∞ := fun x s ↦ if x ≤ s then 1 else 0
  have hg : Measurable (Function.uncurry g) := by
    change Measurable fun p : ℝ × ℝ ↦ if p.1 ≤ p.2 then (1 : ℝ≥0∞) else 0
    exact Measurable.ite (measurableSet_le measurable_fst measurable_snd) measurable_const
      measurable_const
  have h1 : ∀ x ∈ Ioc 1 t, ∫⁻ s in Ioc 1 t, g x s = ENNReal.ofReal (t - x) := by
    intro x hx
    have : (fun s ↦ g x s) = (Ici x).indicator 1 := by
      ext s
      simp [g, indicator_apply]
    rw [this, lintegral_indicator_one measurableSet_Ici, Measure.restrict_apply measurableSet_Ici]
    have : Ici x ∩ Ioc 1 t = Icc x t := by
      ext s
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hx.1.trans_le h.1, h.2⟩⟩
    rw [this, Real.volume_Icc]
  have h2 : ∀ s ∈ Ioc 1 t, ∫⁻ x in Ioc 1 t, g x s ∂μ = μ (Ioc 1 s) := by
    intro s hs
    have : (fun x ↦ g x s) = (Iic s).indicator 1 := by
      ext x
      simp [g, indicator_apply]
    rw [this, lintegral_indicator_one measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.trans hs.2⟩⟩
  calc ∫⁻ x in Ioc 1 t, ENNReal.ofReal (t - x) ∂μ
      = ∫⁻ x in Ioc 1 t, (∫⁻ s in Ioc 1 t, g x s ∂volume) ∂μ :=
        setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ (h1 x hx).symm
    _ = ∫⁻ s in Ioc 1 t, (∫⁻ x in Ioc 1 t, g x s ∂μ) ∂volume :=
        lintegral_lintegral_swap hg.aemeasurable
    _ = ∫⁻ s in Ioc 1 t, μ (Ioc 1 s) := setLIntegral_congr_fun measurableSet_Ioc h2

/-- Tonelli: `∫⁻ x in Ioc t 1, (x - t) ∂μ = ∫⁻ s in Ioc t 1, μ (Ioc s 1)`. -/
lemma setLIntegral_Ioc_sub_left {t : ℝ} (ht : f.xmin < ENNReal.ofReal t) (ht' : t ≤ 1) :
    ∫⁻ x in Ioc t 1, ENNReal.ofReal (x - t) ∂f.rightDerivStieltjes.measure
      = ∫⁻ s in Ioc t 1, f.rightDerivStieltjes.measure (Ioc s 1) := by
  set μ := f.rightDerivStieltjes.measure with hμ_def
  have hμ : IsFiniteMeasure (μ.restrict (Ioc t 1)) := by
    rw [isFiniteMeasure_restrict, hμ_def, ERealStieltjes.measure_Ioc, rightDerivStieltjes_one,
      rightDerivStieltjes_of_mem_interior ht ((ENNReal.ofReal_le_one.mpr ht').trans_lt one_lt_xmax),
      ← EReal.coe_sub, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _)]
    exact ENNReal.ofReal_ne_top
  let g : ℝ → ℝ → ℝ≥0∞ := fun x s ↦ if s < x then 1 else 0
  have hg : Measurable (Function.uncurry g) := by
    change Measurable fun p : ℝ × ℝ ↦ if p.2 < p.1 then (1 : ℝ≥0∞) else 0
    exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst) measurable_const
      measurable_const
  have h1 : ∀ x ∈ Ioc t 1, ∫⁻ s in Ioc t 1, g x s = ENNReal.ofReal (x - t) := by
    intro x hx
    have : (fun s ↦ g x s) = (Iio x).indicator 1 := by
      ext s
      simp [g, indicator_apply]
    rw [this, lintegral_indicator_one measurableSet_Iio, Measure.restrict_apply measurableSet_Iio]
    have : Iio x ∩ Ioc t 1 = Ioo t x := by
      ext s
      simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
      exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.le.trans hx.2⟩⟩
    rw [this, Real.volume_Ioo]
  have h2 : ∀ s ∈ Ioc t 1, ∫⁻ x in Ioc t 1, g x s ∂μ = μ (Ioc s 1) := by
    intro s hs
    have : (fun x ↦ g x s) = (Ioi s).indicator 1 := by
      ext x
      simp [g, indicator_apply]
    rw [this, lintegral_indicator_one measurableSet_Ioi, Measure.restrict_apply measurableSet_Ioi]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hs.1.trans h.1, h.2⟩⟩
  calc ∫⁻ x in Ioc t 1, ENNReal.ofReal (x - t) ∂μ
      = ∫⁻ x in Ioc t 1, (∫⁻ s in Ioc t 1, g x s ∂volume) ∂μ :=
        setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ (h1 x hx).symm
    _ = ∫⁻ s in Ioc t 1, (∫⁻ x in Ioc t 1, g x s ∂μ) ∂volume :=
        lintegral_lintegral_swap hg.aemeasurable
    _ = ∫⁻ s in Ioc t 1, μ (Ioc s 1) := setLIntegral_congr_fun measurableSet_Ioc h2

lemma setLIntegral_Ioc_sub_right_eq_ofReal {t : ℝ} (ht : 1 ≤ t)
    (ht' : ENNReal.ofReal t < f.xmax) :
    ∫⁻ x in Ioc 1 t, ENNReal.ofReal (t - x) ∂f.rightDerivStieltjes.measure
      = ENNReal.ofReal (f.realFun t - rightDeriv f.realFun 1 * (t - 1)) := by
  rw [f.setLIntegral_Ioc_sub_right ht ht']
  have h_eq : ∀ s ∈ Ioc 1 t, f.rightDerivStieltjes.measure (Ioc 1 s)
      = ENNReal.ofReal (rightDeriv f.realFun s - rightDeriv f.realFun 1) := fun s hs ↦
    f.measure_Ioc_one_right hs.1 ((ENNReal.ofReal_le_ofReal hs.2).trans_lt ht')
  rw [setLIntegral_congr_fun measurableSet_Ioc h_eq, ← ofReal_integral_eq_lintegral_ofReal,
    ← intervalIntegral.integral_of_le ht, f.integral_rightDeriv_realFun_sub_one ht ht']
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp
      (f.intervalIntegrable_rightDeriv_realFun ht (by simpa using xmin_lt_one) ht')).sub
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
  · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs ↦ sub_nonneg.mpr ?_
    exact f.rightDeriv_mono hs.1.le (by simpa using xmin_lt_one)
      ((ENNReal.ofReal_le_ofReal hs.2).trans_lt ht')

lemma setLIntegral_Ioc_sub_left_eq_ofReal {t : ℝ} (ht : f.xmin < ENNReal.ofReal t)
    (ht' : t ≤ 1) :
    ∫⁻ x in Ioc t 1, ENNReal.ofReal (x - t) ∂f.rightDerivStieltjes.measure
      = ENNReal.ofReal (f.realFun t + rightDeriv f.realFun 1 * (1 - t)) := by
  rw [f.setLIntegral_Ioc_sub_left ht ht']
  have h_eq : ∀ s ∈ Ioc t 1, f.rightDerivStieltjes.measure (Ioc s 1)
      = ENNReal.ofReal (rightDeriv f.realFun 1 - rightDeriv f.realFun s) := fun s hs ↦
    f.measure_Ioc_one_left (ht.trans_le (ENNReal.ofReal_le_ofReal hs.1.le)) hs.2
  rw [setLIntegral_congr_fun measurableSet_Ioc h_eq, ← ofReal_integral_eq_lintegral_ofReal,
    ← intervalIntegral.integral_of_le ht', f.integral_one_sub_rightDeriv_realFun ht ht']
  · exact (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).sub
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht').mp
        (f.intervalIntegrable_rightDeriv_realFun ht' ht (by simpa using one_lt_xmax)))
  · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs ↦ sub_nonneg.mpr ?_
    exact f.rightDeriv_mono hs.2 (ht.trans_le (ENNReal.ofReal_le_ofReal hs.1.le))
      (by simpa using one_lt_xmax)

lemma realFun_sub_rightDeriv_one_mul_nonneg {t : ℝ} (ht : 1 ≤ t)
    (ht' : ENNReal.ofReal t < f.xmax) :
    0 ≤ f.realFun t - rightDeriv f.realFun 1 * (t - 1) := by
  rw [← f.integral_rightDeriv_realFun_sub_one ht ht']
  refine intervalIntegral.integral_nonneg ht fun u hu ↦ sub_nonneg.mpr ?_
  exact f.rightDeriv_mono hu.1 (by simpa using xmin_lt_one)
    ((ENNReal.ofReal_le_ofReal hu.2).trans_lt ht')

/-- Taylor formula at `1` on the right, inside the effective domain. -/
lemma convex_taylor_one_right_of_lt_xmax {b : ℝ≥0∞} (hb : 1 ≤ b) (hb' : b < f.xmax) :
    f b = ENNReal.ofReal (rightDeriv f.realFun 1) * (b - 1)
      + ∫⁻ x in Ioc 1 b, b - x ∂f.curvatureMeasure := by
  have hb_top : b ≠ ∞ := hb'.ne_top
  have hbt : b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb_top).symm
  have ht1 : 1 ≤ b.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hb_top hb
  have ht' : ENNReal.ofReal b.toReal < f.xmax := by
    rw [← hbt]
    exact hb'
  have h_lint : ∫⁻ x in Ioc 1 b, b - x ∂f.curvatureMeasure
      = ∫⁻ x in Ioc 1 b.toReal, ENNReal.ofReal (b.toReal - x) ∂f.rightDerivStieltjes.measure := by
    rw [curvatureMeasure, setLIntegral_map (f := fun x ↦ b - x) measurableSet_Ioc (by fun_prop)
      ENNReal.measurable_ofReal]
    have h_pre : ENNReal.ofReal ⁻¹' Ioc 1 b = Ioc 1 b.toReal := by
      ext x
      simp only [mem_preimage, mem_Ioc]
      rw [ENNReal.one_lt_ofReal, ENNReal.ofReal_le_iff_le_toReal hb_top]
    rw [h_pre]
    refine setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
    rw [ENNReal.ofReal_sub _ (zero_le_one.trans hx.1.le), ENNReal.ofReal_toReal hb_top]
  rw [h_lint, f.setLIntegral_Ioc_sub_right_eq_ofReal ht1 ht']
  have hfb : f b ≠ ∞ := (lt_top_of_mem_Ioo ⟨xmin_lt_one.trans_le hb, hb'⟩).ne
  calc f b = ENNReal.ofReal (f.realFun b.toReal) := by
        rw [realFun_toReal f hb_top, ENNReal.ofReal_toReal hfb]
  _ = ENNReal.ofReal (rightDeriv f.realFun 1 * (b.toReal - 1)
        + (f.realFun b.toReal - rightDeriv f.realFun 1 * (b.toReal - 1))) := by
        congr 1
        ring
  _ = ENNReal.ofReal (rightDeriv f.realFun 1 * (b.toReal - 1))
        + ENNReal.ofReal (f.realFun b.toReal - rightDeriv f.realFun 1 * (b.toReal - 1)) :=
        ENNReal.ofReal_add (mul_nonneg f.rightDeriv_one_nonneg (sub_nonneg.mpr ht1))
          (f.realFun_sub_rightDeriv_one_mul_nonneg ht1 ht')
  _ = _ := by
        rw [ENNReal.ofReal_mul f.rightDeriv_one_nonneg, ENNReal.ofReal_sub _ zero_le_one,
          ENNReal.ofReal_one, ENNReal.ofReal_toReal hb_top]

/-- Taylor formula at `1` on the left, inside the effective domain. -/
lemma convex_taylor_one_left_of_xmin_lt {b : ℝ≥0∞} (hb : f.xmin < b) (hb' : b ≤ 1) :
    f b + ENNReal.ofReal (rightDeriv f.realFun 1) * (1 - b)
      = ∫⁻ x in Ioc b 1, x - b ∂f.curvatureMeasure := by
  have hb_top : b ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hb'
  have hbt : b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb_top).symm
  have ht0 : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  have ht1 : b.toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top hb'
  have ht' : f.xmin < ENNReal.ofReal b.toReal := by
    rw [← hbt]
    exact hb
  have h_lint : ∫⁻ x in Ioc b 1, x - b ∂f.curvatureMeasure
      = ∫⁻ x in Ioc b.toReal 1, ENNReal.ofReal (x - b.toReal) ∂f.rightDerivStieltjes.measure := by
    rw [curvatureMeasure, setLIntegral_map (f := fun x ↦ x - b) measurableSet_Ioc (by fun_prop)
      ENNReal.measurable_ofReal]
    have h_pre : ENNReal.ofReal ⁻¹' Ioc b 1 = Ioc b.toReal 1 := by
      ext x
      simp only [mem_preimage, mem_Ioc]
      rw [ENNReal.lt_ofReal_iff_toReal_lt hb_top, ENNReal.ofReal_le_one]
    rw [h_pre]
    refine setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
    rw [ENNReal.ofReal_sub _ ht0, ENNReal.ofReal_toReal hb_top]
  rw [h_lint, f.setLIntegral_Ioc_sub_left_eq_ofReal ht' ht1]
  have hfb : f b ≠ ∞ := (lt_top_of_mem_Ioo ⟨hb, hb'.trans_lt one_lt_xmax⟩).ne
  rw [ENNReal.ofReal_add f.realFun_nonneg
    (mul_nonneg f.rightDeriv_one_nonneg (sub_nonneg.mpr ht1)),
    ENNReal.ofReal_mul f.rightDeriv_one_nonneg, ENNReal.ofReal_sub _ ht0, ENNReal.ofReal_one,
    ENNReal.ofReal_toReal hb_top, realFun_toReal f hb_top, ENNReal.ofReal_toReal hfb]

/-- Taylor formula at `1` on the right, for any finite `b ≥ 1`. -/
theorem convex_taylor_one_right' {b : ℝ≥0∞} (hb : 1 ≤ b) (hb_top : b ≠ ∞) :
    f b = ENNReal.ofReal (rightDeriv f.realFun 1) * (b - 1)
      + ∫⁻ x in Ioc 1 b, b - x ∂f.curvatureMeasure := by
  by_cases hb' : b < f.xmax
  · exact f.convex_taylor_one_right_of_lt_xmax hb hb'
  push Not at hb'
  have hxmax : f.xmax ≠ ∞ := ne_top_of_le_ne_top hb_top hb'
  have hfb : f b = ∞ := by
    rcases eq_or_lt_of_le hb' with h | h
    · rw [← h]
      exact apply_xmax_eq_top hxmax
    · exact eq_top_of_xmax_lt h
  rw [hfb]
  -- the right-hand side dominates `f t` for every `t ∈ [1, xmax)`, and `f t → ∞` as `t → xmax`
  symm
  by_contra h_ne
  have h_lt := lt_top_iff_ne_top.mpr h_ne
  have h_ne_bot : (𝓝[<] f.xmax).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Iio' ⟨0, xmax_pos⟩]
    simp
  have h_tendsto : Tendsto f (𝓝[<] f.xmax) (𝓝 ∞) := by
    rw [← apply_xmax_eq_top hxmax]
    exact (f.continuous.tendsto _).mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht_lt, ht⟩ :=
    ((h_tendsto.eventually (Ioi_mem_nhds h_lt)).and (Ioo_mem_nhdsLT one_lt_xmax)).exists
  refine absurd ht_lt (not_lt.mpr ?_)
  rw [f.convex_taylor_one_right_of_lt_xmax ht.1.le ht.2]
  have htb : t ≤ b := ht.2.le.trans hb'
  refine add_le_add (mul_le_mul' le_rfl (tsub_le_tsub_right htb 1)) ?_
  exact (lintegral_mono fun x ↦ tsub_le_tsub_right htb x).trans
    (lintegral_mono_set (Ioc_subset_Ioc_right htb))

/-- Taylor formula at `1` on the left, for any `b ≤ 1`. -/
theorem convex_taylor_one_left' {b : ℝ≥0∞} (hb : b ≤ 1) :
    f b + ENNReal.ofReal (rightDeriv f.realFun 1) * (1 - b)
      = ∫⁻ x in Ioc b 1, x - b ∂f.curvatureMeasure := by
  by_cases hb' : f.xmin < b
  · exact f.convex_taylor_one_left_of_xmin_lt hb' hb
  push Not at hb'
  -- the right-hand side is antitone in `b`
  have h_anti : ∀ t, b ≤ t → ∫⁻ x in Ioc t 1, x - t ∂f.curvatureMeasure
      ≤ ∫⁻ x in Ioc b 1, x - b ∂f.curvatureMeasure := fun t hbt ↦
    (lintegral_mono fun x ↦ tsub_le_tsub_left hbt x).trans
      (lintegral_mono_set (Ioc_subset_Ioc_left hbt))
  rcases eq_or_lt_of_le (zero_le (a := f.xmin)) with hxmin | hxmin
  · -- `xmin = 0`, so `b = 0`: monotone convergence along `t n → 0`
    obtain rfl : b = 0 := le_antisymm (hb'.trans hxmin.symm.le) zero_le
    set t : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (1 / (n + 1)) with ht_def
    have ht_pos : ∀ n, 0 < t n := fun n ↦ ENNReal.ofReal_pos.mpr Nat.one_div_pos_of_nat
    have ht_le : ∀ n, t n ≤ 1 := fun n ↦ by
      rw [ht_def, ENNReal.ofReal_le_one]
      exact (div_le_one (Nat.cast_add_one_pos n)).mpr (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have ht_anti : Antitone t := fun n m hnm ↦ ENNReal.ofReal_le_ofReal
      (one_div_le_one_div_of_le (Nat.cast_add_one_pos n)
        (by exact_mod_cast Nat.add_le_add_right hnm 1))
    have ht_tendsto : Tendsto t atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    have ht_iInf : ⨅ n, t n = 0 := tendsto_nhds_unique (tendsto_atTop_iInf ht_anti) ht_tendsto
    have h_rhs : ∫⁻ x in Ioc 0 1, x - 0 ∂f.curvatureMeasure
        = ⨆ n, ∫⁻ x in Ioc (t n) 1, x - t n ∂f.curvatureMeasure := by
      simp_rw [← lintegral_indicator measurableSet_Ioc]
      rw [← lintegral_iSup]
      · congr 1
        ext x
        by_cases hx : x ∈ Ioc 0 1
        · rw [indicator_of_mem hx, tsub_zero]
          have : ∀ n, (Ioc (t n) 1).indicator (fun y ↦ y - t n) x = x - t n := by
            intro n
            by_cases hxn : x ∈ Ioc (t n) 1
            · rw [indicator_of_mem hxn]
            · rw [indicator_of_notMem hxn, eq_comm, tsub_eq_zero_iff_le]
              exact not_lt.mp fun h ↦ hxn ⟨h, hx.2⟩
          simp_rw [this]
          rw [← ENNReal.sub_iInf, ht_iInf, tsub_zero]
        · rw [indicator_of_notMem hx]
          symm
          exact ENNReal.iSup_eq_zero.mpr fun n ↦
            indicator_of_notMem (fun h ↦ hx ⟨(ht_pos n).trans h.1, h.2⟩) _
      · exact fun n ↦ (measurable_id.sub measurable_const).indicator measurableSet_Ioc
      · intro n m hnm x
        dsimp only
        by_cases hx : x ∈ Ioc (t n) 1
        · have hxm : x ∈ Ioc (t m) 1 := ⟨(ht_anti hnm).trans_lt hx.1, hx.2⟩
          rw [indicator_of_mem hx, indicator_of_mem hxm]
          exact tsub_le_tsub_left (ht_anti hnm) x
        · rw [indicator_of_notMem hx]
          exact zero_le
    have h_lhs : f 0 + ENNReal.ofReal (rightDeriv f.realFun 1) * (1 - 0)
        = ⨆ n, (f (t n) + ENNReal.ofReal (rightDeriv f.realFun 1) * (1 - t n)) := by
      rw [← ENNReal.iSup_add_iSup_of_monotone]
      · congr 1
        · refine tendsto_nhds_unique ((f.continuous.tendsto 0).comp ht_tendsto)
            (tendsto_atTop_iSup fun n m hnm ↦ ?_)
          exact f.antitoneOn (ht_le m) (ht_le n) (ht_anti hnm)
        · rw [← ENNReal.mul_iSup, ← ENNReal.sub_iInf, ht_iInf]
      · exact fun n m hnm ↦ f.antitoneOn (ht_le m) (ht_le n) (ht_anti hnm)
      · exact fun n m hnm ↦ mul_le_mul' le_rfl (tsub_le_tsub_left (ht_anti hnm) 1)
    rw [h_lhs, h_rhs]
    congr 1
    ext n
    refine f.convex_taylor_one_left_of_xmin_lt ?_ (ht_le n)
    rw [← hxmin]
    exact ht_pos n
  · -- `0 < xmin`, so `f b = ∞`: the right-hand side dominates `f t → ∞` as `t → xmin`
    have hfb : f b = ∞ := by
      rcases eq_or_lt_of_le hb' with h | h
      · rw [h]
        exact apply_xmin_eq_top hxmin
      · exact eq_top_of_lt_xmin h
    rw [hfb, top_add]
    symm
    by_contra h_ne
    have h_lt := lt_top_iff_ne_top.mpr h_ne
    have h_ne_bot : (𝓝[>] f.xmin).NeBot := by
      refine mem_closure_iff_nhdsWithin_neBot.mp ?_
      rw [closure_Ioi' ⟨1, xmin_lt_one⟩]
      simp
    have h_tendsto : Tendsto f (𝓝[>] f.xmin) (𝓝 ∞) := by
      rw [← apply_xmin_eq_top hxmin]
      exact (f.continuous.tendsto _).mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht_lt, ht⟩ :=
      ((h_tendsto.eventually (Ioi_mem_nhds h_lt)).and (Ioo_mem_nhdsGT xmin_lt_one)).exists
    refine absurd ht_lt (not_lt.mpr ?_)
    calc f t ≤ f t + ENNReal.ofReal (rightDeriv f.realFun 1) * (1 - t) := le_self_add
    _ = ∫⁻ x in Ioc t 1, x - t ∂f.curvatureMeasure :=
        f.convex_taylor_one_left_of_xmin_lt ht.1 ht.2.le
    _ ≤ _ := h_anti t (hb'.trans ht.1.le)

theorem convex_taylor_one_right (hf : rightDeriv f.realFun 1 = 0) {b : ℝ≥0∞} (hb : 1 ≤ b)
    (hb_top : b ≠ ∞) :
    f b = ∫⁻ x in Ioc 1 b, b - x ∂f.curvatureMeasure := by
  rw [f.convex_taylor_one_right' hb hb_top, hf, ENNReal.ofReal_zero, zero_mul, zero_add]

theorem convex_taylor_one_left (hf : rightDeriv f.realFun 1 = 0) {b : ℝ≥0∞} (hb : b ≤ 1) :
    f b = ∫⁻ x in Ioc b 1, x - b ∂f.curvatureMeasure := by
  have h := f.convex_taylor_one_left' hb
  rwa [hf, ENNReal.ofReal_zero, zero_mul, add_zero] at h

noncomputable
def curvatureMeasureReal (f : DivFunction) : Measure ℝ := f.curvatureMeasure.map ENNReal.toReal

lemma curvatureMeasureReal_apply (f : DivFunction) {s : Set ℝ} (hs : MeasurableSet s) :
    f.curvatureMeasureReal s = f.curvatureMeasure (ENNReal.toReal ⁻¹' s) := by
  rw [curvatureMeasureReal, Measure.map_apply (by fun_prop) hs]

instance : SFinite f.curvatureMeasure := by
  rw [curvatureMeasure]
  infer_instance

instance : SFinite f.curvatureMeasureReal := by
  rw [curvatureMeasureReal]
  infer_instance

lemma lintegral_curvatureMeasureReal (f : DivFunction) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂f.curvatureMeasureReal = ∫⁻ x, g x.toReal ∂f.curvatureMeasure := by
  unfold curvatureMeasureReal
  rw [lintegral_map hg (by fun_prop)]

lemma integral_curvatureMeasureReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : DivFunction) {g : ℝ → E} (hg : StronglyMeasurable g) :
    ∫ x, g x ∂f.curvatureMeasureReal = ∫ x, g x.toReal ∂f.curvatureMeasure := by
  unfold curvatureMeasureReal
  rw [integral_map _ hg.aestronglyMeasurable]
  exact Measurable.aemeasurable (by fun_prop)

lemma setLIntegral_curvatureMeasureReal (f : DivFunction) {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂f.curvatureMeasureReal
      = ∫⁻ x in ENNReal.toReal ⁻¹' s, g x.toReal ∂f.curvatureMeasure := by
  unfold curvatureMeasureReal
  rw [setLIntegral_map hs hg (by fun_prop)]

lemma setIntegral_curvatureMeasureReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : DivFunction) {g : ℝ → E} (hg : StronglyMeasurable g) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂f.curvatureMeasureReal
      = ∫ x in ENNReal.toReal ⁻¹' s, g x.toReal ∂f.curvatureMeasure := by
  unfold curvatureMeasureReal
  rw [setIntegral_map hs hg.aestronglyMeasurable]
  exact Measurable.aemeasurable (by fun_prop)

lemma setLIntegral_Ioc_curvatureMeasureReal (f : DivFunction) {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    {a b : ℝ} (h : 0 ≤ a) :
    ∫⁻ x in Ioc a b, g x ∂f.curvatureMeasureReal
      = ∫⁻ x in Ioc (ENNReal.ofReal a) (ENNReal.ofReal b), g x.toReal ∂f.curvatureMeasure := by
  rw [setLIntegral_curvatureMeasureReal f hg measurableSet_Ioc, ENNReal.preimage_toReal_Ioc h]

lemma setIntegral_Ioc_curvatureMeasureReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : DivFunction) {g : ℝ → E} (hg : StronglyMeasurable g) {a b : ℝ}
    (h : 0 ≤ a) :
    ∫ x in Ioc a b, g x ∂f.curvatureMeasureReal
      = ∫ x in Ioc (ENNReal.ofReal a) (ENNReal.ofReal b), g x.toReal ∂f.curvatureMeasure := by
  rw [setIntegral_curvatureMeasureReal f hg measurableSet_Ioc, ENNReal.preimage_toReal_Ioc h]

lemma integrable_curvatureMeasureReal_sub_iff_ne_top_of_ge (hf : rightDeriv f.realFun 1 = 0)
    {b : ℝ} (hb : 1 ≤ b) :
    IntegrableOn (fun x ↦ b - x) (Ioc 1 b) f.curvatureMeasureReal ↔ f (ENNReal.ofReal b) ≠ ∞ := by
  have : EqOn (fun x ↦ b - x) (fun x ↦ (ENNReal.ofReal b - ENNReal.ofReal x).toReal)
      (Ioc 1 b) := by
    intro x hx
    simp only
    rw [ENNReal.toReal_sub_of_le _ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal,
      ENNReal.toReal_ofReal]
    · exact zero_le_one.trans hx.1.le
    · positivity
    · exact ENNReal.ofReal_le_ofReal hx.2
  rw [integrableOn_congr_fun this measurableSet_Ioc, IntegrableOn, integrable_toReal_iff]
  rotate_left
  · exact Measurable.aemeasurable (by fun_prop)
  · refine ae_of_all _ fun x ↦ (tsub_le_self.trans_lt ENNReal.ofReal_lt_top).ne
  rw [setLIntegral_Ioc_curvatureMeasureReal f (by fun_prop) zero_le_one, ENNReal.ofReal_one]
  have : ∫⁻ x in Ioc 1 (ENNReal.ofReal b),
        ENNReal.ofReal b - ENNReal.ofReal x.toReal ∂f.curvatureMeasure
      = ∫⁻ x in Ioc 1 (ENNReal.ofReal b), ENNReal.ofReal b - x ∂f.curvatureMeasure := by
    refine setLIntegral_congr_fun_ae measurableSet_Ioc <| ae_of_all _ fun x hx ↦ ?_
    rw [ENNReal.ofReal_toReal]
    refine (hx.2.trans_lt ?_).ne
    exact ENNReal.ofReal_lt_top
  rw [this, convex_taylor_one_right hf (ENNReal.one_le_ofReal.mpr hb) ENNReal.ofReal_ne_top]

lemma integrable_curvatureMeasureReal_sub_iff_ne_top_of_le (hf : rightDeriv f.realFun 1 = 0)
    {b : ℝ} (hb_nonneg : 0 ≤ b) (hb : b ≤ 1) :
    IntegrableOn (fun x ↦ x - b) (Ioc b 1) f.curvatureMeasureReal ↔ f (ENNReal.ofReal b) ≠ ∞ := by
  have : EqOn (fun x ↦ x - b) (fun x ↦ (ENNReal.ofReal x - ENNReal.ofReal b).toReal)
      (Ioc b 1) := by
    intro x hx
    simp only
    rw [ENNReal.toReal_sub_of_le _ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal,
      ENNReal.toReal_ofReal]
    · positivity
    · exact hb_nonneg.trans hx.1.le
    · exact ENNReal.ofReal_le_ofReal hx.1.le
  rw [integrableOn_congr_fun this measurableSet_Ioc, IntegrableOn, integrable_toReal_iff]
  rotate_left
  · exact Measurable.aemeasurable (by fun_prop)
  · refine ae_of_all _ fun x ↦ (tsub_le_self.trans_lt ENNReal.ofReal_lt_top).ne
  rw [setLIntegral_Ioc_curvatureMeasureReal f (by fun_prop) hb_nonneg, ENNReal.ofReal_one]
  have : ∫⁻ x in Ioc (ENNReal.ofReal b) 1,
        ENNReal.ofReal x.toReal - ENNReal.ofReal b ∂f.curvatureMeasure
      = ∫⁻ x in Ioc (ENNReal.ofReal b) 1, x - ENNReal.ofReal b ∂f.curvatureMeasure := by
    refine setLIntegral_congr_fun_ae measurableSet_Ioc <| ae_of_all _ fun x hx ↦ ?_
    rw [ENNReal.ofReal_toReal]
    refine (hx.2.trans_lt ?_).ne
    exact ENNReal.one_lt_top
  rw [this, convex_taylor_one_left hf]
  simp [hb]

theorem convex_taylor_one_right_real (hf : rightDeriv f.realFun 1 = 0) {b : ℝ} (hb : 1 ≤ b) :
    f.realFun b = ∫ x in Ioc 1 b, b - x ∂f.curvatureMeasureReal := by
  rw [← ENNReal.ofReal_eq_ofReal_iff]
  rotate_left
  · exact f.realFun_nonneg
  · exact setIntegral_nonneg measurableSet_Ioc fun x hx ↦ sub_nonneg_of_le hx.2
  rw [setIntegral_Ioc_curvatureMeasureReal f _ zero_le_one, ENNReal.ofReal_one]
  swap; · refine Measurable.stronglyMeasurable ?_; fun_prop
  have : ∫ x in Ioc 1 (ENNReal.ofReal b), b - x.toReal ∂f.curvatureMeasure
      = ∫ x in Ioc 1 (ENNReal.ofReal b), (ENNReal.ofReal b - x).toReal ∂f.curvatureMeasure := by
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
    rw [ENNReal.toReal_sub_of_le hx.2 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (zero_le_one.trans hb)]
  rw [this, integral_toReal]
  rotate_left
  · exact Measurable.aemeasurable (by fun_prop)
  · exact ae_of_all _ fun x ↦ tsub_le_self.trans_lt ENNReal.ofReal_lt_top
  rw [← convex_taylor_one_right hf (ENNReal.one_le_ofReal.mpr hb) ENNReal.ofReal_ne_top, realFun]

theorem convex_taylor_one_left_real (hf : rightDeriv f.realFun 1 = 0) {b : ℝ}
    (hb_zero : 0 ≤ b) (hb : b ≤ 1) :
    f.realFun b = ∫ x in Ioc b 1, x - b ∂f.curvatureMeasureReal := by
  rw [← ENNReal.ofReal_eq_ofReal_iff]
  rotate_left
  · exact f.realFun_nonneg
  · exact setIntegral_nonneg measurableSet_Ioc fun x hx ↦ sub_nonneg_of_le hx.1.le
  rw [setIntegral_Ioc_curvatureMeasureReal f _ hb_zero, ENNReal.ofReal_one]
  swap; · refine Measurable.stronglyMeasurable ?_; fun_prop
  have : ∫ x in Ioc (ENNReal.ofReal b) 1, x.toReal - b ∂f.curvatureMeasure
      = ∫ x in Ioc (ENNReal.ofReal b) 1, (x - ENNReal.ofReal b).toReal ∂f.curvatureMeasure := by
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
    rw [ENNReal.toReal_sub_of_le hx.1.le (hx.2.trans_lt ENNReal.one_lt_top).ne,
      ENNReal.toReal_ofReal hb_zero]
  rw [this, integral_toReal]
  rotate_left
  · exact Measurable.aemeasurable (by fun_prop)
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact ae_of_all _ fun x hx ↦ tsub_le_self.trans_lt (hx.2.trans_lt ENNReal.one_lt_top)
  rw [← convex_taylor_one_left hf, realFun]
  simp [hb]

theorem convex_taylor_one (hf : rightDeriv f.realFun 1 = 0) {b : ℝ} (hb_zero : 0 ≤ b) :
    f.realFun b = ∫ x in (1)..b, b - x ∂f.curvatureMeasureReal := by
  rcases le_or_gt 1 b with hb | hb
  · simp only [intervalIntegral, not_lt, hb, Ioc_eq_empty, Measure.restrict_empty,
      integral_zero_measure, sub_zero]
    exact convex_taylor_one_right_real hf hb
  · simp only [intervalIntegral, not_lt, hb.le, Ioc_eq_empty, Measure.restrict_empty,
      integral_zero_measure, zero_sub]
    simp only [← integral_neg, neg_sub]
    exact convex_taylor_one_left_real hf hb_zero hb.le

end ConvexTaylor

end DivFunction

end ProbabilityTheory

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.FDiv.DivFunction.DerivAtTop

/-!

# f-Divergences functions

-/

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}
  {f : ℝ → ℝ}

namespace DivFunction

section OfReal

section OfRealFun

/-- The function `ℝ≥0∞ → ℝ≥0∞` underlying `DivFunction.ofReal`: it is `ENNReal.ofReal ∘ f` on
`(0, ∞)`, extended by its limits at `0` and `∞` to ensure continuity. -/
noncomputable
def ofRealFun (f : ℝ → ℝ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = 0 then Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0
  else if x = ∞ then limsup (fun x ↦ ENNReal.ofReal (f x)) atTop
  else ENNReal.ofReal (f x.toReal)

@[simp]
lemma ofRealFun_zero : ofRealFun f 0 = Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 := by
  simp [ofRealFun]

@[simp]
lemma ofRealFun_top : ofRealFun f ∞ = limsup (fun x ↦ ENNReal.ofReal (f x)) atTop := by
  simp [ofRealFun]

lemma ofRealFun_apply {x : ℝ≥0∞} (hx_zero : x ≠ 0) (hx_top : x ≠ ∞) :
    ofRealFun f x = ENNReal.ofReal (f x.toReal) := by
  simp [ofRealFun, hx_zero, hx_top]

/-- If `f` is convex on `(0, ∞)` with `f 1 = 0`, then `max f 0` is nonincreasing on `(0, 1]`. -/
lemma _root_.ConvexOn.antitoneOn_ofReal_comp (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) :
    AntitoneOn (fun x ↦ ENNReal.ofReal (f x)) (Ioc 0 1) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hy.2 with rfl | hy1
  · simp [hf_one]
  by_cases hfy : f y ≤ 0
  · simp [ENNReal.ofReal_of_nonpos hfy]
  refine ENNReal.ofReal_le_ofReal ?_
  refine hf.le_left_of_right_le'' hx.1 (mem_Ioi.mpr one_pos) hxy hy1 ?_
  rw [hf_one]
  exact (not_le.mp hfy).le

/-- If `f` is convex on `(0, ∞)` with `f 1 = 0`, then `max f 0` is nondecreasing on `[1, ∞)`. -/
lemma _root_.ConvexOn.monotoneOn_ofReal_comp (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) :
    MonotoneOn (fun x ↦ ENNReal.ofReal (f x)) (Ici 1) := by
  intro x hx y _ hxy
  rcases eq_or_lt_of_le (mem_Ici.mp hx) with rfl | hx1
  · simp [hf_one]
  by_cases hfx : f x ≤ 0
  · simp [ENNReal.ofReal_of_nonpos hfx]
  refine ENNReal.ofReal_le_ofReal ?_
  refine hf.le_right_of_left_le'' (mem_Ioi.mpr one_pos)
    (mem_Ioi.mpr (zero_lt_one.trans (hx1.trans_le hxy))) hx1 hxy ?_
  rw [hf_one]
  exact (not_le.mp hfx).le

lemma tendsto_ofReal_comp_nhdsGT_zero (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) :
    Tendsto (fun x ↦ ENNReal.ofReal (f x)) (𝓝[>] 0) (𝓝 (ofRealFun f 0)) := by
  rw [ofRealFun_zero]
  -- `ENNReal.ofReal ∘ f` is antitone on `(0, 1]`: extend it to `(0, ∞)` by capping at 1
  have h_anti : AntitoneOn (fun x ↦ ENNReal.ofReal (f (min x 1))) (Ioi 0) := by
    intro x hx y hy hxy
    exact hf.antitoneOn_ofReal_comp hf_one ⟨lt_min hx one_pos, min_le_right _ _⟩
      ⟨lt_min hy one_pos, min_le_right _ _⟩ (min_le_min_right _ hxy)
  have h_tendsto := h_anti.tendsto_nhdsGT (OrderTop.bddAbove _)
  have h_eq : (fun x ↦ ENNReal.ofReal (f (min x 1)))
      =ᶠ[𝓝[>] (0 : ℝ)] fun x ↦ ENNReal.ofReal (f x) := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
    simp [min_eq_left hx.2.le]
  rw [rightLim_eq_of_tendsto (h_tendsto.congr' h_eq)]
  exact h_tendsto.congr' h_eq

lemma tendsto_ofReal_comp_atTop (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) :
    Tendsto (fun x ↦ ENNReal.ofReal (f x)) atTop (𝓝 (ofRealFun f ∞)) := by
  rw [ofRealFun_top]
  obtain ⟨y, hy⟩ := ENNReal.tendsto_of_monotoneOn (hf.monotoneOn_ofReal_comp hf_one)
  rw [hy.limsup_eq]
  exact hy

lemma continuous_ofRealFun (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) :
    Continuous (ofRealFun f) := by
  have h_cont : ContinuousOn f (Ioi 0) := hf.continuousOn isOpen_Ioi
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases hx0 : x = 0
  · subst hx0
    rw [continuousAt_iff_continuous_left_right]
    refine ⟨?_, ?_⟩
    · rw [← ENNReal.bot_eq_zero, Iic_bot]
      exact continuousWithinAt_singleton
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have h_toReal : Tendsto ENNReal.toReal (𝓝[>] (0 : ℝ≥0∞)) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact tendsto_nhdsWithin_of_tendsto_nhds
          (by simpa using ENNReal.tendsto_toReal ENNReal.zero_ne_top)
      · filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ENNReal.zero_lt_top)] with y hy hy_top
        exact ENNReal.toReal_pos hy.ne' hy_top.ne
    change Tendsto (ofRealFun f) (𝓝[>] 0) (𝓝 (ofRealFun f 0))
    refine ((tendsto_ofReal_comp_nhdsGT_zero hf hf_one).comp h_toReal).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ENNReal.zero_lt_top)] with y hy hy_top
    simp [ofRealFun_apply hy.ne' hy_top.ne]
  by_cases hx_top : x = ∞
  · subst hx_top
    rw [continuousAt_iff_continuous_left_right]
    refine ⟨?_, ?_⟩
    swap
    · rw [Ici_top]
      exact continuousWithinAt_singleton
    rw [← continuousWithinAt_Iio_iff_Iic]
    have h_toReal : Tendsto ENNReal.toReal (𝓝[<] (∞ : ℝ≥0∞)) atTop := by
      refine tendsto_atTop.mpr fun b ↦ ?_
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ENNReal.ofReal_lt_top)] with y hy hy_gt
      exact (ENNReal.ofReal_le_iff_le_toReal hy.ne).mp hy_gt.le
    change Tendsto (ofRealFun f) (𝓝[<] ∞) (𝓝 (ofRealFun f ∞))
    refine ((tendsto_ofReal_comp_atTop hf hf_one).comp h_toReal).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ENNReal.zero_lt_top)] with y hy hy_pos
    simp [ofRealFun_apply hy_pos.ne' hy.ne]
  have h1 : ContinuousAt (fun y : ℝ≥0∞ ↦ ENNReal.ofReal (f y.toReal)) x :=
    ENNReal.continuous_ofReal.continuousAt.comp
      ((h_cont.continuousAt (Ioi_mem_nhds (ENNReal.toReal_pos hx0 hx_top))).comp
        (ENNReal.continuousAt_toReal hx_top))
  refine h1.congr ?_
  filter_upwards [Ioo_mem_nhds (pos_iff_ne_zero.mpr hx0) (lt_top_iff_ne_top.mpr hx_top)] with y hy
  exact (ofRealFun_apply hy.1.ne' hy.2.ne).symm

lemma convexOn_ofRealFun (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) :
    ConvexOn ℝ≥0 univ (ofRealFun f) := by
  have h_cont := continuous_ofRealFun hf hf_one
  refine ⟨convex_univ, fun x _ y _ a b _ _ hab ↦ ?_⟩
  -- the convexity inequality on `(0, ∞) × (0, ∞)` follows from the convexity of `f`
  have h_Ioo : ∀ x ∈ Ioo (0 : ℝ≥0∞) ∞, ∀ y ∈ Ioo (0 : ℝ≥0∞) ∞,
      ofRealFun f (a • x + b • y) ≤ a • ofRealFun f x + b • ofRealFun f y := by
    intro x hx y hy
    have hxy_top : a • x + b • y ≠ ∞ := by
      simp only [ENNReal.smul_def, smul_eq_mul]
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hx.2.ne,
        ENNReal.mul_ne_top ENNReal.coe_ne_top hy.2.ne⟩
    have hxy_zero : a • x + b • y ≠ 0 := by
      intro h
      rw [add_eq_zero, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_eq_zero,
        mul_eq_zero] at h
      simp only [ENNReal.coe_eq_zero, hx.1.ne', hy.1.ne', or_false] at h
      simp [h.1, h.2] at hab
    have h_toReal : (a • x + b • y).toReal = a * x.toReal + b * y.toReal := by
      simp only [ENNReal.smul_def, smul_eq_mul]
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hx.2.ne)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top hy.2.ne), ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.coe_toReal, ENNReal.coe_toReal]
    rw [ofRealFun_apply hxy_zero hxy_top, ofRealFun_apply hx.1.ne' hx.2.ne,
      ofRealFun_apply hy.1.ne' hy.2.ne, h_toReal]
    have h_cvx := hf.2 (mem_Ioi.mpr (ENNReal.toReal_pos hx.1.ne' hx.2.ne))
      (mem_Ioi.mpr (ENNReal.toReal_pos hy.1.ne' hy.2.ne)) a.coe_nonneg b.coe_nonneg
      (by rw [← NNReal.coe_add, hab, NNReal.coe_one])
    simp only [smul_eq_mul] at h_cvx
    calc ENNReal.ofReal (f (a * x.toReal + b * y.toReal))
      _ ≤ ENNReal.ofReal (a * f x.toReal + b * f y.toReal) := ENNReal.ofReal_le_ofReal h_cvx
      _ ≤ ENNReal.ofReal (a * f x.toReal) + ENNReal.ofReal (b * f y.toReal) :=
        ENNReal.ofReal_add_le
      _ = a • ENNReal.ofReal (f x.toReal) + b • ENNReal.ofReal (f y.toReal) := by
        rw [ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_mul b.coe_nonneg,
          ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def,
          ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
  -- the inequality is a closed condition and `(0, ∞) × (0, ∞)` is dense
  have h_closed : IsClosed {p : ℝ≥0∞ × ℝ≥0∞ |
      ofRealFun f (a • p.1 + b • p.2) ≤ a • ofRealFun f p.1 + b • ofRealFun f p.2} := by
    simp only [ENNReal.smul_def, smul_eq_mul]
    refine isClosed_le ?_ ?_
    · exact h_cont.comp (((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp continuous_fst).add
        ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp continuous_snd))
    · exact Continuous.add
        ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp (h_cont.comp continuous_fst))
        ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp (h_cont.comp continuous_snd))
  have h_subset : Ioo (0 : ℝ≥0∞) ∞ ×ˢ Ioo (0 : ℝ≥0∞) ∞ ⊆ {p : ℝ≥0∞ × ℝ≥0∞ |
      ofRealFun f (a • p.1 + b • p.2) ≤ a • ofRealFun f p.1 + b • ofRealFun f p.2} :=
    fun p hp ↦ h_Ioo p.1 hp.1 p.2 hp.2
  have h_closure : closure (Ioo (0 : ℝ≥0∞) ∞ ×ˢ Ioo (0 : ℝ≥0∞) ∞) = univ := by
    rw [closure_prod_eq, closure_Ioo ENNReal.zero_ne_top, ← ENNReal.bot_eq_zero, Icc_bot_top,
      univ_prod_univ]
  have h := h_closed.closure_subset_iff.mpr h_subset
  rw [h_closure] at h
  exact h (mem_univ (x, y))

end OfRealFun

/-- Build a `DivFunction` from a function `f : ℝ → ℝ` which is convex on `Ioi 0` and satisfies
`f 1 = 0`. On `(0, ∞)` it is `ENNReal.ofReal ∘ f`, extended by its limits at `0` and `∞`. -/
noncomputable
def ofReal (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ioi 0) f) (hf_one : f 1 = 0) : DivFunction where
  toFun := ofRealFun f
  one := by simp [ofRealFun, hf_one]
  convexOn' := convexOn_ofRealFun hf hf_one
  continuous' := continuous_ofRealFun hf hf_one

variable {hf : ConvexOn ℝ (Ioi 0) f} {hf_one : f 1 = 0}

section OfRealApply

@[simp]
lemma ofReal_apply_zero :
    ofReal f hf hf_one 0 = Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 := by
  simp [ofReal]

lemma ofReal_apply_zero_of_continuousWithinAt (hf_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ofReal f hf hf_one 0 = ENNReal.ofReal (f 0) := by
  simp only [ofReal_apply_zero]
  refine rightLim_eq_of_tendsto ?_
  refine ContinuousWithinAt.tendsto ?_
  exact (ENNReal.continuous_ofReal.tendsto _).comp hf_cont.tendsto

@[simp]
lemma ofReal_apply_top :
    ofReal f hf hf_one ∞ = limsup (fun x ↦ ENNReal.ofReal (f x)) atTop := by
  simp [ofReal]

lemma ofReal_apply_top_of_tendsto_atTop (h : Tendsto f atTop atTop) :
    ofReal f hf hf_one ∞ = ∞ := by
  rw [ofReal_apply_top]
  refine Tendsto.limsup_eq ?_
  rwa [ENNReal.tendsto_ofReal_nhds_top]

lemma ofReal_apply {x : ℝ≥0∞} (hx_zero : x ≠ 0) (hx_top : x ≠ ∞) :
    ofReal f hf hf_one x = ENNReal.ofReal (f x.toReal) := by
  simp [ofReal, ofRealFun_apply hx_zero hx_top]

lemma ofReal_apply_of_continuousWithinAt (hf_cont : ContinuousWithinAt f (Ioi 0) 0)
    {x : ℝ≥0∞} (hx : x ≠ ∞) :
    ofReal f hf hf_one x = ENNReal.ofReal (f x.toReal) := by
  by_cases hx0 : x = 0
  · simp [hx0, ofReal_apply_zero_of_continuousWithinAt hf_cont]
  · exact ofReal_apply hx0 hx

lemma realFun_ofReal_apply (hf_nonneg : ∀ x, 0 < x → 0 ≤ f x) {x : ℝ} (hx : 0 < x) :
    (ofReal f hf hf_one).realFun x = f x := by
  rw [realFun, ofReal_apply (by simp [hx]) (by simp), ENNReal.toReal_ofReal hx.le,
    ENNReal.toReal_ofReal (hf_nonneg x hx)]

end OfRealApply

section DerivAtTop

lemma ofReal_apply_ne_top {x : ℝ≥0∞} (hx : 0 < x) (hx' : x ≠ ∞) :
    ofReal f hf hf_one x ≠ ∞ := by
  rw [ofReal_apply hx.ne' hx']
  exact ENNReal.ofReal_ne_top

@[simp] lemma xmin_ofReal : (ofReal f hf hf_one).xmin = 0 :=
  xmin_eq_zero fun _ hx hx' ↦ ofReal_apply_ne_top hx hx'

@[simp] lemma xmax_ofReal : (ofReal f hf hf_one).xmax = ∞ :=
  xmax_eq_top fun _ hx hx' ↦ ofReal_apply_ne_top hx hx'

lemma rightDerivStieltjes_ofReal_eventuallyEq (hf_nonneg : ∀ x, 0 < x → 0 ≤ f x) :
    (ofReal f hf hf_one).rightDerivStieltjes =ᶠ[atTop] fun x ↦ (rightDeriv f x : EReal) := by
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [rightDerivStieltjes_of_mem_interior (by simp [hx]) (by simp)]
  congr 1
  refine Filter.EventuallyEq.rightDeriv_eq_nhds ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact realFun_ofReal_apply hf_nonneg hy

/-- The `derivAtTop` of `ofReal f hf hf_one` is the (real function) `derivAtTop` of `f`. -/
lemma derivAtTop_ofReal_eq_toENNReal (hf_nonneg : ∀ x, 0 < x → 0 ≤ f x) :
    (ofReal f hf hf_one).derivAtTop = (_root_.derivAtTop f).toENNReal := by
  rw [DivFunction.derivAtTop, _root_.derivAtTop,
    limsup_congr (rightDerivStieltjes_ofReal_eventuallyEq hf_nonneg)]

lemma derivAtTop_ofReal (hf_nonneg : ∀ x, 0 < x → 0 ≤ f x) :
    (ofReal f hf hf_one).derivAtTop
      = limsup (fun x ↦ ENNReal.ofReal (rightDeriv f x)) atTop := by
  rw [derivAtTop_ofReal_eq_toENNReal hf_nonneg]
  have h_mono : MonotoneOn (rightDeriv f) (Ioi 0) := by
    have h := hf.monotoneOn_rightDeriv
    rwa [interior_Ioi] at h
  have h_tendsto : Tendsto (fun x ↦ ENNReal.ofReal (rightDeriv f x)) atTop
      (𝓝 (_root_.derivAtTop f).toENNReal) := by
    refine ((EReal.continuous_toENNReal.tendsto _).comp h_mono.tendsto_derivAtTop).congr
      fun x ↦ ?_
    simp only [Function.comp_apply]
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  exact h_tendsto.limsup_eq.symm

lemma derivAtTop_ofReal_ne_top (hf_nonneg : ∀ x, 0 < x → 0 ≤ f x)
    (h_lim : limsup (fun x ↦ ENNReal.ofReal (rightDeriv f x)) atTop ≠ ∞) :
    (ofReal f hf hf_one).derivAtTop ≠ ∞ := by
  rwa [derivAtTop_ofReal hf_nonneg]

lemma derivAtTop_ofReal_of_tendsto_nhds (hf_nonneg : ∀ x, 0 < x → 0 ≤ f x) {y : ℝ}
    (h : Tendsto (rightDeriv f) atTop (𝓝 y)) :
    (ofReal f hf hf_one).derivAtTop = ENNReal.ofReal y := by
  rw [derivAtTop_ofReal_eq_toENNReal hf_nonneg, derivAtTop_of_tendsto_nhds h,
    EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma derivAtTop_ofReal_of_tendsto_atTop (hf_nonneg : ∀ x, 0 < x → 0 ≤ f x)
    (h : Tendsto (rightDeriv f) atTop atTop) :
    (ofReal f hf hf_one).derivAtTop = ∞ := by
  rw [derivAtTop_ofReal_eq_toENNReal hf_nonneg, derivAtTop_of_tendsto_atTop h,
    EReal.toENNReal_top]

end DerivAtTop

section Integral

lemma lintegral_ofReal_eq_top_of_not_integrable [SigmaFinite μ] [IsFiniteMeasure ν]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h_int : ¬ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    ∫⁻ x, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν = ∞ := by
  refine lintegral_eq_top_of_not_integrable_realFun ?_
  suffices ¬ IntegrableOn
      (fun x ↦ (ofReal f hf hf_one).realFun (μ.rnDeriv ν x).toReal)
      {x | μ.rnDeriv ν x ≠ 0} ν from
    fun h ↦ this h.integrableOn
  rw [← integrableOn_univ] at h_int
  have : (univ : Set α) = {x | μ.rnDeriv ν x ≠ 0} ∪ {x | μ.rnDeriv ν x = 0} :=
    (compl_union_self _).symm
  rw [this, integrableOn_union] at h_int
  have h_int_zero : IntegrableOn (fun x ↦ f (μ.rnDeriv ν x).toReal) {x | μ.rnDeriv ν x = 0} ν := by
    refine (integrableOn_congr_fun ?_ ?_).mpr
      (integrableOn_const (C := f 0) (measure_ne_top _ _))
    · intro x hx
      simp only [mem_ofPred_eq] at hx
      simp [hx]
    · exact μ.measurable_rnDeriv ν (measurableSet_singleton 0)
  simp only [ne_eq, h_int_zero, and_true] at h_int
  convert h_int using 1
  refine integrableOn_congr_fun_ae ((ae_restrict_iff' ?_).mpr ?_)
  · exact (μ.measurable_rnDeriv ν (measurableSet_singleton 0)).compl
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx_top hx_zero
  rw [DivFunction.realFun_ofReal_apply fun x hx ↦ hf_nonneg x hx.le]
  exact ENNReal.toReal_pos hx_zero hx_top

lemma lintegral_ofReal' [SigmaFinite μ] (h : ν {x | μ.rnDeriv ν x = 0} ≠ ∞) :
    ∫⁻ x, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν
        - ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0}
        + Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 * ν {x | μ.rnDeriv ν x = 0} := by
  let s := {x | μ.rnDeriv ν x = 0}
  have hs : MeasurableSet s := μ.measurable_rnDeriv ν (measurableSet_singleton 0)
  rw [← lintegral_add_compl _ hs]
  have hs_zero : ∀ x ∈ s, μ.rnDeriv ν x = 0 := fun _ hx ↦ hx
  have h1 : ∫⁻ x in s, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 * ν {x | μ.rnDeriv ν x = 0} := by
    have : ∀ x ∈ s, ofReal f hf hf_one (μ.rnDeriv ν x)
        = Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 := by
      intro x hx
      simp [hs_zero x hx]
    rw [setLIntegral_congr_fun_ae hs (ae_of_all _ this)]
    rw [setLIntegral_const]
  have h2 : ∫⁻ x in sᶜ, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x in sᶜ, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν := by
    refine setLIntegral_congr_fun_ae hs.compl ?_
    filter_upwards [μ.rnDeriv_ne_top ν] with x hx_top hx
    rw [ofReal_apply hx hx_top]
  have h3 : ∫⁻ x in s, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν
      = ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0} := by
    have : ∀ x ∈ s, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal)
        = ENNReal.ofReal (f 0) := by
      intro x hx
      simp [hs_zero x hx]
    rw [setLIntegral_congr_fun_ae hs (ae_of_all _ this)]
    rw [setLIntegral_const]
  rw [h1, h2, ← h3]
  conv_rhs => rw [← lintegral_add_compl _ hs (μ := ν), add_comm]
  congr 1
  rw [h3, ENNReal.add_sub_cancel_left]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h

lemma lintegral_ofReal [SigmaFinite μ] [IsFiniteMeasure ν] :
    ∫⁻ x, DivFunction.ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν
        - ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0}
        + Function.rightLim (fun x ↦ ENNReal.ofReal (f x)) 0 * ν {x | μ.rnDeriv ν x = 0} :=
  DivFunction.lintegral_ofReal' (measure_ne_top _ _)

lemma lintegral_ofReal_of_continuous [SigmaFinite μ]
    (hf_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ∫⁻ x, DivFunction.ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν := by
  let s := {x | μ.rnDeriv ν x = 0}
  have hs : MeasurableSet s := μ.measurable_rnDeriv ν (measurableSet_singleton 0)
  rw [← lintegral_add_compl _ hs, ← lintegral_add_compl _ hs (μ := ν)]
  have hs_zero : ∀ x ∈ s, μ.rnDeriv ν x = 0 := fun _ hx ↦ hx
  have h1 : ∫⁻ x in s, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0} := by
    have : ∀ x ∈ s, ofReal f hf hf_one (μ.rnDeriv ν x) = ENNReal.ofReal (f 0) := by
      intro x hx
      rw [hs_zero x hx, ofReal_apply_zero_of_continuousWithinAt hf_cont]
    rw [setLIntegral_congr_fun_ae hs (ae_of_all _ this)]
    rw [setLIntegral_const]
  have h2 : ∫⁻ x in sᶜ, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ∫⁻ x in sᶜ, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν := by
    refine setLIntegral_congr_fun_ae hs.compl ?_
    filter_upwards [μ.rnDeriv_ne_top ν] with x hx_top hx
    rw [ofReal_apply hx hx_top]
  have h3 : ∫⁻ x in s, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) ∂ν
      = ENNReal.ofReal (f 0) * ν {x | μ.rnDeriv ν x = 0} := by
    have : ∀ x ∈ s, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal) = ENNReal.ofReal (f 0) := by
      intro x hx
      simp [hs_zero x hx]
    rw [setLIntegral_congr_fun_ae hs (ae_of_all _ this)]
    rw [setLIntegral_const]
  rw [h1, h2, h3]

lemma lintegral_ofReal_eq_integral_of_continuous [SigmaFinite μ]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hf_cont : ContinuousWithinAt f (Ioi 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    ∫⁻ x, DivFunction.ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν
      = ENNReal.ofReal (∫ x, f (μ.rnDeriv ν x).toReal ∂ν) := by
  rw [DivFunction.lintegral_ofReal_of_continuous hf_cont,
    ofReal_integral_eq_lintegral_ofReal h_int]
  refine ae_of_all _ fun x ↦ hf_nonneg _ ENNReal.toReal_nonneg

lemma measurable_comp_rnDeriv_of_convexOn_of_continuous
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) (h_cont : ContinuousWithinAt f (Ioi 0) 0) :
    Measurable (fun x ↦ f (μ.rnDeriv ν x).toReal) := by
  have : (fun x ↦ f (μ.rnDeriv ν x).toReal)
      = (fun x : Ici (0 : ℝ) ↦ f x)
        ∘ (fun x ↦ ⟨(μ.rnDeriv ν x).toReal, ENNReal.toReal_nonneg⟩) := rfl
  rw [this]
  have h1 : Measurable (fun x : Ici (0 : ℝ) ↦ f x) := by
    refine Continuous.measurable ?_
    refine continuousOn_iff_continuous_domRestrict.mp ?_
    have h_Ioi : ContinuousOn f (Ioi 0) := hf.continuousOn isOpen_Ioi
    rw [ContinuousOn]
    intro x hx
    by_cases h0 : x = 0
    · rw [h0, ← continuousWithinAt_Ioi_iff_Ici]
      exact h_cont
    · have h := h_Ioi.continuousWithinAt (lt_of_le_of_ne hx (Ne.symm h0))
      refine (h.continuousAt ?_).continuousWithinAt
      exact Ioi_mem_nhds (lt_of_le_of_ne hx (Ne.symm h0))
  exact h1.comp (μ.measurable_rnDeriv ν).ennreal_toReal.subtype_mk

lemma lintegral_ofReal_ne_top_iff_integrable_of_continuous [SigmaFinite μ]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ∫⁻ x, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν ≠ ∞
      ↔ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν := by
  rw [lintegral_ofReal_of_continuous h_cont, lintegral_ofReal_ne_top_iff_integrable]
  · refine Measurable.aestronglyMeasurable ?_
    exact measurable_comp_rnDeriv_of_convexOn_of_continuous hf h_cont
  · exact ae_of_all _ fun x ↦ hf_nonneg _ ENNReal.toReal_nonneg

lemma lintegral_ofReal_eq_top_iff_not_integrable_of_continuous [SigmaFinite μ]
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ∫⁻ x, ofReal f hf hf_one (μ.rnDeriv ν x) ∂ν = ∞
      ↔ ¬ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν := by
  rw [← lintegral_ofReal_ne_top_iff_integrable_of_continuous hf_nonneg h_cont, not_not]

end Integral

end OfReal

section OfConvexOn

lemma _root_.ConvexOn.sub_one (hf : ConvexOn ℝ (Ioi 0) f) :
    ConvexOn ℝ (Ioi 0) fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1) := by
  have h_eq x : f x - f 1 - rightDeriv f 1 * (x - 1)
      = f x + (- rightDeriv f 1) * x + (- f 1 + rightDeriv f 1) := by ring
  simp_rw [h_eq, add_assoc]
  refine hf.add ?_
  refine ConvexOn.add ?_ (convexOn_const _ (convex_Ioi _))
  exact (ConvexOn.const_mul_id _).subset (subset_univ _) (convex_Ioi _)

lemma rightDeriv_sub_one (hf : DifferentiableWithinAt ℝ f (Ioi 1) 1) :
    rightDeriv (fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1)) 1 = 0 := by
  have h_eq x : f x - f 1 - rightDeriv f 1 * (x - 1)
      = f x + (- rightDeriv f 1) * x + (- f 1 + rightDeriv f 1) := by ring
  simp_rw [h_eq]
  rw [rightDeriv_add_const_apply, rightDeriv_add_linear_apply hf]
  · ring
  · exact hf.add ((differentiableWithinAt_const _).mul differentiableWithinAt_id)

lemma _root_.ConvexOn.rightDeriv_sub_one (hf : ConvexOn ℝ (Ioi 0) f) :
    rightDeriv (fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1)) 1 = 0 :=
  DivFunction.rightDeriv_sub_one (hf.differentiableWithinAt_Ioi_of_mem_interior (by simp))

/-- A convex function lies above its tangent line at `1`. -/
lemma _root_.ConvexOn.sub_one_nonneg (hf : ConvexOn ℝ (Ioi 0) f) {x : ℝ} (hx : 0 < x) :
    0 ≤ f x - f 1 - rightDeriv f 1 * (x - 1) := by
  have h := hf.affine_le_of_mem_interior
    ((interior_Ioi (a := (0 : ℝ))).symm ▸ mem_Ioi.mpr zero_lt_one) hx
  nlinarith

lemma rightDeriv_sub_one_apply (hf : ConvexOn ℝ (Ioi 0) f) {x : ℝ} (hx : 0 < x) :
    rightDeriv (fun y ↦ f y - f 1 - rightDeriv f 1 * (y - 1)) x
      = rightDeriv f x - rightDeriv f 1 := by
  have h_eq : (fun y ↦ f y - f 1 - rightDeriv f 1 * (y - 1))
      = fun y ↦ f y + (- rightDeriv f 1) * y + (- f 1 + rightDeriv f 1) := by ext; ring
  have hd : DifferentiableWithinAt ℝ f (Ioi x) x :=
    hf.differentiableWithinAt_Ioi_of_mem_interior (by rw [interior_Ioi]; exact hx)
  rw [h_eq, rightDeriv_add_const_apply, rightDeriv_add_linear_apply hd]
  · ring
  · exact hd.add ((differentiableWithinAt_const _).mul differentiableWithinAt_id)

-- todo: give a default value 0 when f is not convex?
/-- Build a `DivFunction` from a function `f : ℝ → ℝ` which is convex on `Ioi 0`. -/
noncomputable
def ofConvexOn (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ioi 0) f) : DivFunction :=
  ofReal (fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1)) hf.sub_one (by simp)

section OfConvexOnApply

variable {hf : ConvexOn ℝ (Ioi 0) f}

@[simp]
lemma ofConvexOn_apply_zero :
    ofConvexOn f hf 0
      = Function.rightLim (fun x ↦ ENNReal.ofReal (f x - f 1 - rightDeriv f 1 * (x - 1))) 0 := by
  simp [ofConvexOn]

lemma ofConvexOn_apply_zero_of_continuousWithinAt (hf_cont : ContinuousWithinAt f (Ioi 0) 0) :
    ofConvexOn f hf 0 = ENNReal.ofReal (f 0 - f 1 + rightDeriv f 1) := by
  rw [ofConvexOn, ofReal_apply_zero_of_continuousWithinAt]
  · simp
  · simp_rw [← sub_add_eq_sub_sub]
    refine hf_cont.sub ?_
    exact continuousWithinAt_const.add
      (continuousWithinAt_const.mul (continuousWithinAt_id.sub continuousWithinAt_const))

@[simp]
lemma ofConvexOn_apply_top :
    ofConvexOn f hf ∞
      = limsup (fun x ↦ ENNReal.ofReal (f x - f 1 - rightDeriv f 1 * (x - 1))) atTop := by
  simp [ofConvexOn]

lemma ofConvexOn_apply {x : ℝ≥0∞} (hx_zero : x ≠ 0) (hx_top : x ≠ ∞) :
    ofConvexOn f hf x = ENNReal.ofReal (f x.toReal - f 1 - rightDeriv f 1 * (x.toReal - 1)) := by
  simp [ofConvexOn, ofReal_apply, hx_zero, hx_top]

end OfConvexOnApply

end OfConvexOn

variable {f g : DivFunction}

section DerivAtTop

lemma derivAtTop_ofConvexOn {f : ℝ → ℝ} {hf : ConvexOn ℝ (Ioi 0) f} :
    (ofConvexOn f hf).derivAtTop
      = limsup (fun x ↦ ENNReal.ofReal (rightDeriv f x - rightDeriv f 1)) atTop := by
  rw [ofConvexOn, derivAtTop_ofReal fun x hx ↦ hf.sub_one_nonneg hx]
  refine limsup_congr ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [rightDeriv_sub_one_apply hf hx]

lemma derivAtTop_ofConvexOn_of_tendsto_atTop {f : ℝ → ℝ} {hf : ConvexOn ℝ (Ioi 0) f}
    (h : Tendsto (rightDeriv f) atTop atTop) :
    (ofConvexOn f hf).derivAtTop = ∞ := by
  rw [ofConvexOn]
  refine derivAtTop_ofReal_of_tendsto_atTop (fun x hx ↦ hf.sub_one_nonneg hx) ?_
  have h_eq : rightDeriv (fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1))
      =ᶠ[atTop] fun x ↦ rightDeriv f x + (- rightDeriv f 1) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [rightDeriv_sub_one_apply hf hx, sub_eq_add_neg]
  rw [tendsto_congr' h_eq]
  exact tendsto_atTop_add_const_right atTop _ h

end DerivAtTop

end DivFunction

variable {f : DivFunction}

end ProbabilityTheory

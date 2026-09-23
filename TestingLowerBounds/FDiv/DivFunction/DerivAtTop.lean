/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import TestingLowerBounds.FDiv.DivFunction.RightDeriv

/-!

# f-Divergences functions

-/

@[expose] public section

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

namespace DivFunction

variable {f g : DivFunction}

/-- Limit at `+∞` of the right derivative of `f`, as an element of `ℝ≥0∞`. -/
noncomputable
def derivAtTop (f : DivFunction) : ℝ≥0∞ := (limsup f.rightDerivStieltjes atTop).toENNReal

lemma limsup_rightDerivStieltjes_atTop_nonneg :
    0 ≤ limsup f.rightDerivStieltjes atTop := by
  refine le_limsup_of_frequently_le <| Eventually.frequently ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  exact rightDerivStieltjes_one_nonneg.trans (f.rightDerivStieltjes.mono ha)

lemma tendsto_rightDerivStieltjes_atTop :
    Tendsto f.rightDerivStieltjes atTop (𝓝 f.derivAtTop) := by
  rw [derivAtTop, EReal.coe_toENNReal limsup_rightDerivStieltjes_atTop_nonneg]
  have hy := tendsto_atTop_iSup f.rightDerivStieltjes.mono
  rwa [hy.limsup_eq]

lemma rightDerivStieltjes_le_derivAtTop (x : ℝ) : f.rightDerivStieltjes x ≤ f.derivAtTop :=
  f.rightDerivStieltjes.mono.ge_of_tendsto tendsto_rightDerivStieltjes_atTop x

lemma derivAtTop_eq_top_of_xmax_ne_top (h : f.xmax ≠ ∞) : f.derivAtTop = ∞ := by
  have h_le := f.rightDerivStieltjes_le_derivAtTop f.xmax.toReal
  rwa [rightDerivStieltjes_of_ge_xmax (by rw [ENNReal.ofReal_toReal h]), top_le_iff,
    EReal.coe_ennreal_eq_top_iff] at h_le

lemma xmax_eq_top_of_derivAtTop_ne_top (h : f.derivAtTop ≠ ∞) : f.xmax = ∞ := by
  by_contra h_top
  exact h (derivAtTop_eq_top_of_xmax_ne_top h_top)

lemma rightDeriv_realFun_le_toReal_derivAtTop (h : f.derivAtTop ≠ ∞) {x : ℝ}
    (hx : f.xmin < ENNReal.ofReal x) (hx' : ENNReal.ofReal x < f.xmax) :
    rightDeriv f.realFun x ≤ f.derivAtTop.toReal := by
  have h1 := f.rightDerivStieltjes_le_derivAtTop x
  rwa [rightDerivStieltjes_of_mem_interior hx hx', ← EReal.coe_ennreal_toReal h,
    EReal.coe_le_coe_iff] at h1

@[simp]
lemma derivAtTop_zero : derivAtTop (0 : DivFunction) = 0 := by
  simp only [derivAtTop, rightDerivStieltjes_zero, EReal.toENNReal_eq_zero_iff]
  have : (fun x ↦ if x < (0 : ℝ) then (⊥ : EReal) else 0) =ᶠ[atTop] fun _ ↦ 0 := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [ite_eq_right (not_lt.mpr hx)]
  rw [limsup_congr this]
  simp

/-- Two `DivFunction`s that coincide in a (left) neighborhood of `∞` have the same `derivAtTop`. -/
lemma derivAtTop_congr (h : (f : ℝ≥0∞ → ℝ≥0∞) =ᶠ[𝓝[<] ∞] g) : f.derivAtTop = g.derivAtTop := by
  obtain ⟨c, hc, hc_sub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' ENNReal.zero_lt_top).mp h
  have hc' : c ≠ ∞ := hc.ne
  have h_eq : ∀ z, c < z → z ≠ ∞ → f z = g z := fun z hz hz' ↦ hc_sub ⟨hz, hz'.lt_top⟩
  -- the effective domains coincide beyond `c`
  have h_xmax : ∀ (f g : DivFunction), (∀ z, c < z → z ≠ ∞ → f z = g z) → ∀ x : ℝ,
      c < ENNReal.ofReal x → f.xmax ≤ ENNReal.ofReal x → g.xmax ≤ ENNReal.ofReal x := by
    intro f g h_eq x hcx hf
    rw [xmax]
    refine sSup_le fun z hz ↦ ?_
    by_contra hz_lt
    push Not at hz_lt
    by_cases hz_top : z = ∞
    · subst hz_top
      have h_mem : ENNReal.ofReal x + 1 ∈ {z | f z ≠ ∞} := by
        rw [mem_ofPred_eq,
          h_eq _ (hcx.trans (ENNReal.lt_add_right ENNReal.ofReal_ne_top one_ne_zero))
          (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩)]
        exact ne_top_of_le_ne_top hz
          (g.monotoneOn (mem_Ici.mpr le_add_self) (mem_Ici.mpr le_top) le_top)
      exact absurd ((le_sSup h_mem).trans hf)
        (not_le.mpr (ENNReal.lt_add_right ENNReal.ofReal_ne_top one_ne_zero))
    · have h_mem : z ∈ {z | f z ≠ ∞} := by
        rw [mem_ofPred_eq, h_eq z (hcx.trans hz_lt) hz_top]
        exact hz
      exact absurd ((le_sSup h_mem).trans hf) (not_le.mpr hz_lt)
  have h_rds : f.rightDerivStieltjes =ᶠ[atTop] g.rightDerivStieltjes := by
    filter_upwards [eventually_ge_atTop (max 1 (c.toReal + 1))] with x hx
    have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
    have hcx : c < ENNReal.ofReal x := by
      rw [ENNReal.lt_ofReal_iff_toReal_lt hc']
      linarith [(le_max_right _ _).trans hx]
    by_cases hf_top : f.xmax ≤ ENNReal.ofReal x
    · rw [rightDerivStieltjes_of_ge_xmax hf_top,
        rightDerivStieltjes_of_ge_xmax (h_xmax f g h_eq x hcx hf_top)]
    by_cases hg_top : g.xmax ≤ ENNReal.ofReal x
    · exact absurd (h_xmax g f (fun z hz hz' ↦ (h_eq z hz hz').symm) x hcx hg_top) hf_top
    push Not at hf_top hg_top
    rw [rightDerivStieltjes_eq_rightLim (xmin_toReal_lt_one.le.trans hx1) hf_top,
      rightDerivStieltjes_eq_rightLim (xmin_toReal_lt_one.le.trans hx1) hg_top]
    refine rightLim_congr (NeBot.ne inferInstance)
      (f.tendsto_rightDeriv_realFun_nhdsGT (xmin_toReal_lt_one.le.trans hx1) hf_top) ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : x < y)
    show ((rightDeriv f.realFun y : ℝ) : EReal) = rightDeriv g.realFun y
    congr 1
    refine Filter.EventuallyEq.rightDeriv_eq_nhds ?_
    have hcy : c.toReal < y := by linarith [(le_max_right _ _).trans hx]
    filter_upwards [Ioi_mem_nhds hcy] with y' (hy' : c.toReal < y')
    simp only [realFun]
    rw [h_eq _ ((ENNReal.lt_ofReal_iff_toReal_lt hc').mpr hy') ENNReal.ofReal_ne_top]
  rw [derivAtTop, derivAtTop, limsup_congr h_rds]

lemma derivAtTop_congr_nonneg (h : ∀ x, f x = g x) : f.derivAtTop = g.derivAtTop := by
  rw [DivFunction.ext h]

@[simp]
lemma derivAtTop_add : (f + g).derivAtTop = f.derivAtTop + g.derivAtTop := by
  have h_add : Tendsto (fun x ↦ f.rightDerivStieltjes x + g.rightDerivStieltjes x) atTop
      (𝓝 (f.derivAtTop + g.derivAtTop)) :=
    (EReal.continuousAt_add (Or.inr (EReal.coe_ennreal_ne_bot _))
      (Or.inl (EReal.coe_ennreal_ne_bot _))).tendsto.comp
      (f.tendsto_rightDerivStieltjes_atTop.prodMk_nhds g.tendsto_rightDerivStieltjes_atTop)
  have h_eq : (f + g).rightDerivStieltjes
      =ᶠ[atTop] fun x ↦ f.rightDerivStieltjes x + g.rightDerivStieltjes x := by
    rw [rightDerivStieltjes_add]
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hf_bot : f.rightDerivStieltjes x ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot
      (rightDerivStieltjes_one_nonneg.trans (f.rightDerivStieltjes.mono hx))
    have hg_bot : g.rightDerivStieltjes x ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot
      (rightDerivStieltjes_one_nonneg.trans (g.rightDerivStieltjes.mono hx))
    by_cases hf_top : f.rightDerivStieltjes x = ⊤
    · rw [ERealStieltjes.add_apply_of_eq_top_left hf_top, hf_top, EReal.top_add_of_ne_bot hg_bot]
    by_cases hg_top : g.rightDerivStieltjes x = ⊤
    · rw [ERealStieltjes.add_apply_of_eq_top_right hg_top, hg_top, EReal.add_top_of_ne_bot hf_bot]
    exact ERealStieltjes.add_apply_of_ne_top hf_top hg_top
  rw [derivAtTop, (h_add.congr' h_eq.symm).limsup_eq, ← EReal.coe_ennreal_add, EReal.toENNReal_coe]

@[simp]
lemma derivAtTop_smul {c : ℝ≥0} : (c • f).derivAtTop = c * f.derivAtTop := by
  by_cases hc : c = 0
  · simp [hc]
  have h_tendsto : Tendsto (fun x ↦ ((c : ℝ) : EReal) * f.rightDerivStieltjes x) atTop
      (𝓝 (((c : ℝ) : EReal) * f.derivAtTop)) :=
    (EReal.continuous_coe_mul.tendsto _).comp f.tendsto_rightDerivStieltjes_atTop
  have h_eq : (c • f).rightDerivStieltjes
      =ᶠ[atTop] fun x ↦ ((c : ℝ) : EReal) * f.rightDerivStieltjes x := by
    rw [rightDerivStieltjes_smul hc]
    exact .of_forall fun x ↦ by rw [ERealStieltjes.smul_apply, EReal.coe_nnreal_eq_coe_real]
  rw [derivAtTop, (h_tendsto.congr' h_eq.symm).limsup_eq,
    EReal.toENNReal_mul (EReal.coe_nonneg.mpr c.coe_nonneg), EReal.toENNReal_coe]
  congr 1
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe, ENNReal.ofReal_coe_nnreal]

/-- Core case of `le_add_derivAtTop`: `y` and `x` in the interior of the effective domain. -/
lemma le_add_derivAtTop_of_mem_Ioo (h : f.derivAtTop ≠ ∞) {x y : ℝ≥0∞}
    (hy : f.xmin < y) (hyx : y < x) (hx : x ≠ ∞) :
    f x ≤ f y + f.derivAtTop * (x - y) := by
  have hx_max : f.xmax = ∞ := xmax_eq_top_of_derivAtTop_ne_top h
  have hy_top : y ≠ ∞ := ne_top_of_lt hyx
  have hfx : f x ≠ ∞ := (lt_top_of_mem_Ioo ⟨hy.trans hyx, hx_max ▸ hx.lt_top⟩).ne
  have hfy : f y ≠ ∞ := (lt_top_of_mem_Ioo ⟨hy, hx_max ▸ hy_top.lt_top⟩).ne
  have hy_mem : y.toReal ∈ ENNReal.toReal '' Ioo f.xmin f.xmax :=
    ⟨y, ⟨hy, hx_max ▸ hy_top.lt_top⟩, rfl⟩
  have hx_mem : x.toReal ∈ ENNReal.toReal '' Ioo f.xmin f.xmax :=
    ⟨x, ⟨hy.trans hyx, hx_max ▸ hx.lt_top⟩, rfl⟩
  have hx_int : x.toReal ∈ interior (ENNReal.toReal '' Ioo f.xmin f.xmax) := by
    rw [f.isOpen_toReal_Ioo.interior_eq]
    exact hx_mem
  have hxy' : y.toReal < x.toReal := ENNReal.toReal_strict_mono hx hyx
  have h_slope : f.realFun x.toReal - f.realFun y.toReal
      ≤ f.derivAtTop.toReal * (x.toReal - y.toReal) := by
    have h1 := f.convexOn_Ioo_realFun.slope_le_leftDeriv_of_mem_interior hy_mem hx_int hxy'
    have h2 := f.convexOn_Ioo_realFun.leftDeriv_le_rightDeriv_of_mem_interior hx_int
    have h3 := f.rightDeriv_realFun_le_toReal_derivAtTop h (mem_toReal_Ioo_iff.mp hx_mem).1
      (mem_toReal_Ioo_iff.mp hx_mem).2
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hxy')] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (h2.trans h3) (sub_nonneg.mpr hxy'.le))
  calc f x = ENNReal.ofReal (f.realFun x.toReal) := by
        rw [realFun_toReal f hx, ENNReal.ofReal_toReal hfx]
  _ ≤ ENNReal.ofReal (f.realFun y.toReal + f.derivAtTop.toReal * (x.toReal - y.toReal)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
  _ ≤ ENNReal.ofReal (f.realFun y.toReal)
        + ENNReal.ofReal (f.derivAtTop.toReal * (x.toReal - y.toReal)) := ENNReal.ofReal_add_le
  _ = f y + f.derivAtTop * (x - y) := by
        rw [realFun_toReal f hy_top, ENNReal.ofReal_toReal hfy,
          ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal h,
          ← ENNReal.toReal_sub_of_le hyx.le hx, ENNReal.ofReal_toReal (ENNReal.sub_ne_top hx)]

lemma le_add_derivAtTop_of_ne_top {x y : ℝ≥0∞} (hyx : y ≤ x) (hx : x ≠ ∞) :
    f x ≤ f y + f.derivAtTop * (x - y) := by
  rcases eq_or_lt_of_le hyx with rfl | hyx
  · simp
  by_cases h : f.derivAtTop = ∞
  · rw [h, ENNReal.top_mul (tsub_pos_iff_lt.mpr hyx).ne']
    simp
  by_cases hfy : f y = ∞
  · simp [hfy]
  have hy_min : f.xmin ≤ y := not_lt.mp fun hy ↦ hfy (eq_top_of_lt_xmin hy)
  rcases eq_or_lt_of_le hy_min with hy_eq | hy_lt
  swap; · exact f.le_add_derivAtTop_of_mem_Ioo h hy_lt hyx hx
  -- `y = f.xmin`, and `f y ≠ ∞` forces `f.xmin = 0`
  have hy0 : y = 0 := by
    by_contra hy0
    apply hfy
    rw [← hy_eq]
    exact apply_xmin_eq_top (by rw [hy_eq]; exact pos_iff_ne_zero.mpr hy0)
  subst hy0
  have h_ne_bot : (𝓝[>] (0 : ℝ≥0∞)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ioi' ⟨1, zero_lt_one⟩]
    simp
  have h_cont : Tendsto (fun y ↦ f y + f.derivAtTop * (x - y)) (𝓝[>] 0)
      (𝓝 (f 0 + f.derivAtTop * (x - 0))) :=
    ((f.continuous.add ((ENNReal.continuous_const_mul h).comp
      (ENNReal.continuous_sub_left hx))).tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto h_cont ?_
  filter_upwards [Ioo_mem_nhdsGT hyx] with y hy
  refine f.le_add_derivAtTop_of_mem_Ioo h ?_ hy.2 hx
  rw [hy_eq]
  exact hy.1

lemma le_add_derivAtTop {x y : ℝ≥0∞} (hyx : y ≤ x) :
    f x ≤ f y + f.derivAtTop * (x - y) := by
  by_cases hx : x = ∞
  swap; · exact f.le_add_derivAtTop_of_ne_top hyx hx
  subst hx
  by_cases hy : y = ∞
  · simp [hy]
  by_cases hd : f.derivAtTop = 0
  · simp only [hd, zero_mul, add_zero]
    have h_ne_bot : (𝓝[<] (∞ : ℝ≥0∞)).NeBot := by
      refine mem_closure_iff_nhdsWithin_neBot.mp ?_
      rw [closure_Iio' ⟨0, ENNReal.zero_lt_top⟩]
      simp
    refine le_of_tendsto ((f.continuous.tendsto ∞).mono_left (nhdsWithin_le_nhds (s := Iio ∞))) ?_
    filter_upwards [Ioo_mem_nhdsLT (lt_top_iff_ne_top.mpr hy)] with z hz
    simpa [hd] using f.le_add_derivAtTop_of_ne_top hz.1.le hz.2.ne
  · rw [ENNReal.top_sub hy, ENNReal.mul_top hd]
    simp

lemma le_add_derivAtTop'' (x y : ℝ≥0∞) :
    f (x + y) ≤ f x + f.derivAtTop * y := by
  by_cases hx : x = ∞
  · simp [hx]
  have := f.le_add_derivAtTop (le_self_add : x ≤ x + y)
  rwa [ENNReal.add_sub_cancel_left hx] at this

lemma le_add_derivAtTop' (x : ℝ≥0∞) {u : ℝ≥0∞} (hu' : u ≤ 1) :
    f x ≤ f (x * u) + f.derivAtTop * x * (1 - u) := by
  have : x = x * u + x * (1 - u) := by
    rw [← mul_add]
    rw [add_tsub_cancel_of_le hu', mul_one]
  conv_lhs => rw [this]
  refine (le_add_derivAtTop'' (x * u) (x * (1 - u))).trans ?_
  rw [mul_assoc]

/-- For `1 ≤ y`, `f y ≤ f.derivAtTop * y`. -/
lemma apply_le_derivAtTop_mul {y : ℝ≥0∞} (hy : 1 ≤ y) : f y ≤ f.derivAtTop * y := by
  have h := f.le_add_derivAtTop'' 1 (y - 1)
  rw [add_tsub_cancel_of_le hy, apply_one, zero_add] at h
  refine h.trans ?_
  gcongr
  exact tsub_le_self

/-- `f y / y` tends to `f.derivAtTop` as `y → ∞`. -/
lemma tendsto_div_nhdsLT_top : Tendsto (fun y ↦ f y / y) (𝓝[<] ∞) (𝓝 f.derivAtTop) := by
  refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · by_cases h_max : f.xmax = ∞
    swap
    · filter_upwards [Ioo_mem_nhdsLT (lt_top_iff_ne_top.2 h_max)] with y hy
      rw [eq_top_of_xmax_lt hy.1, ENNReal.top_div_of_ne_top hy.2.ne]
      exact hc.trans_le le_top
    have hc_top : c ≠ ∞ := hc.ne_top
    have hc' : (c : EReal) < (f.derivAtTop : EReal) := EReal.coe_ennreal_lt_coe_ennreal_iff.2 hc
    obtain ⟨x₀, hx₀, hx₀c⟩ := (((tendsto_order.1 f.tendsto_rightDerivStieltjes_atTop).1 c hc').and
      (eventually_gt_atTop (max 1 f.xmin.toReal))).exists
    have hx₀1 : 1 < x₀ := (le_max_left _ _).trans_lt hx₀c
    have hx₀_nonneg : 0 ≤ x₀ := zero_le_one.trans hx₀1.le
    have hx₀_min : f.xmin < ENNReal.ofReal x₀ := by
      rw [ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top]
      exact (le_max_right _ _).trans_lt hx₀c
    have hx₀_max : ENNReal.ofReal x₀ < f.xmax := h_max ▸ ENNReal.ofReal_lt_top
    rw [rightDerivStieltjes_of_mem_interior hx₀_min hx₀_max] at hx₀
    set d := rightDeriv f.realFun x₀ with hd
    have hcd : c.toReal < d := by
      rw [← EReal.coe_ennreal_toReal hc_top] at hx₀
      exact_mod_cast hx₀
    have hd_nonneg : 0 ≤ d := ENNReal.toReal_nonneg.trans hcd.le
    set D := ENNReal.ofReal d with hD
    have hcD : c < D := by rwa [hD, ENNReal.lt_ofReal_iff_toReal_lt hc_top]
    set x := ENNReal.ofReal x₀ with hx
    have hx_top : x ≠ ∞ := ENNReal.ofReal_ne_top
    -- tangent inequality: `D * (y - x) ≤ f y`
    have h_key : ∀ y, y ≠ ∞ → D * (y - x) ≤ f y := by
      intro y hy
      have h := f.apply_add_le_apply_add ⟨hx₀_min, hx₀_max⟩ hy
      rw [ENNReal.toReal_ofReal hx₀_nonneg, ← hd, max_eq_left hd_nonneg,
        max_eq_right (neg_nonpos.2 hd_nonneg), ENNReal.ofReal_zero, zero_mul, add_zero, zero_mul,
        add_zero, ← hD] at h
      rw [ENNReal.mul_sub (fun _ _ ↦ ENNReal.ofReal_ne_top), tsub_le_iff_right]
      exact le_add_self.trans h
    -- `D * (y - x) / y → D`
    have h1 : Tendsto (fun y ↦ x / y) (𝓝[<] ∞) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul
        ((continuous_inv.tendsto ∞).mono_left (nhdsWithin_le_nhds (s := Iio ∞)))
        (Or.inr hx_top) (a := x)
      simpa [div_eq_mul_inv] using this
    have h2 : Tendsto (fun y ↦ D * (1 - x / y)) (𝓝[<] ∞) (𝓝 D) := by
      have := ENNReal.Tendsto.const_mul
        (ENNReal.Tendsto.sub tendsto_const_nhds h1 (Or.inl ENNReal.one_ne_top))
        (Or.inl (by simp)) (a := D)
      simpa using this
    have h_eq : ∀ᶠ y in 𝓝[<] ∞, D * (1 - x / y) = D * (y - x) / y := by
      filter_upwards [Ioo_mem_nhdsLT ENNReal.zero_lt_top] with y hy
      rw [mul_div_assoc, ENNReal.sub_div (fun _ _ ↦ hy.1.ne'), ENNReal.div_self hy.1.ne' hy.2.ne]
    filter_upwards [(tendsto_order.1 h2).1 c hcD, h_eq, Ioo_mem_nhdsLT ENNReal.zero_lt_top]
      with y h1 h2 hy
    calc c < D * (1 - x / y) := h1
      _ = D * (y - x) / y := h2
      _ ≤ f y / y := ENNReal.div_le_div_right (h_key y hy.2.ne) y
  · filter_upwards [Ioo_mem_nhdsLT ENNReal.one_lt_top] with y hy
    refine lt_of_le_of_lt ?_ hc
    rw [ENNReal.div_le_iff (zero_lt_one.trans hy.1).ne' hy.2.ne]
    exact f.apply_le_derivAtTop_mul hy.1.le

/-- `derivAtTop` is monotone: if `f ≤ g` pointwise, then `f.derivAtTop ≤ g.derivAtTop`. -/
lemma derivAtTop_mono (hfg : ∀ x, f x ≤ g x) : f.derivAtTop ≤ g.derivAtTop := by
  have : (𝓝[<] (∞ : ℝ≥0∞)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ENNReal.zero_lt_top⟩
  exact le_of_tendsto_of_tendsto' f.tendsto_div_nhdsLT_top g.tendsto_div_nhdsLT_top
    fun y ↦ ENNReal.div_le_div_right (hfg y) y

lemma lintegral_comp_rnDeriv_ne_top (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hf_zero : f 0 ≠ ∞) (hf_deriv : f.derivAtTop ≠ ∞) :
    ∫⁻ x, f (μ.rnDeriv ν x) ∂ν ≠ ∞ := by
  have h x : f (μ.rnDeriv ν x) ≤ f 0 + f.derivAtTop * μ.rnDeriv ν x := by
    simpa using f.le_add_derivAtTop'' 0 (μ.rnDeriv ν x)
  refine ne_top_of_le_ne_top ?_ (lintegral_mono h)
  rw [lintegral_add_left measurable_const, lintegral_const,
    lintegral_const_mul _ (μ.measurable_rnDeriv ν)]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hf_zero (measure_ne_top _ _),
    ENNReal.mul_ne_top hf_deriv ?_⟩
  exact ne_top_of_le_ne_top (measure_ne_top μ _) Measure.lintegral_rnDeriv_le

end DivFunction

variable {f : DivFunction}

end ProbabilityTheory

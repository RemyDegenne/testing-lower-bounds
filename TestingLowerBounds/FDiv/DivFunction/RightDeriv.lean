/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import TestingLowerBounds.DerivAtTop
public import TestingLowerBounds.FDiv.DivFunction.Basic
public import TestingLowerBounds.ForMathlib.ERealStieltjes
public import TestingLowerBounds.ForMathlib.RnDeriv

/-!
# Right derivative of a divergence function

For a divergence function `f`, we define `f.rightDerivStieltjes`, the right derivative of `f` as a
monotone right-continuous function `ℝ → EReal` (an `ERealStieltjes` function). It is `⊥` below
`f.xmin`, `⊤` from `f.xmax` on, and it agrees with the right derivative of `f.realFun` in the
interior of the effective domain of `f`.

## Main statements

* `rightDerivStieltjes_of_mem_interior`: in the interior of the effective domain,
  `f.rightDerivStieltjes x = rightDeriv f.realFun x`.
* `rightDerivStieltjes_eq_top_iff`: `f.rightDerivStieltjes x = ⊤ ↔ f.xmax ≤ ENNReal.ofReal x`.
* `rightDerivStieltjes_xmin_eq_bot_iff`: `f.rightDerivStieltjes` is `⊥` at `f.xmin` iff the right
  derivative of `f.realFun` tends to `-∞` there.
* `rightDerivStieltjes_add`, `rightDerivStieltjes_smul`: compatibility with the module structure.

-/

@[expose] public section

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace DivFunction

variable {f g : DivFunction}

section RightDeriv

lemma continuousWithinAt_rightDeriv (f : DivFunction) {x : ℝ}
    (hx : f.xmin < ENNReal.ofReal x) (hx' : ENNReal.ofReal x < f.xmax) :
    ContinuousWithinAt (rightDeriv f.realFun) (Ici x) x := by
  refine f.convexOn_Ioo_realFun.rightDeriv_right_continuous_of_mem_interior ?_
  rw [f.isOpen_toReal_Ioo.interior_eq]
  exact mem_toReal_Ioo_iff.mpr ⟨hx, hx'⟩

/-- Auxiliary monotone function: `⊥` up to `f.xmin`, `⊤` from `f.xmax` on, and the right
derivative of `f.realFun` in between. `f.rightDerivStieltjes` is its right-continuous
regularization. -/
noncomputable def rightDerivAux (f : DivFunction) : ℝ → EReal := fun x ↦
  if x ≤ f.xmin.toReal then ⊥
  else if f.xmax ≤ ENNReal.ofReal x then ⊤
  else (rightDeriv f.realFun x : EReal)

lemma monotone_rightDerivAux (f : DivFunction) : Monotone f.rightDerivAux := by
  intro x y hxy
  by_cases hx1 : x ≤ f.xmin.toReal
  · simp [rightDerivAux, hx1]
  have hy1 : ¬ y ≤ f.xmin.toReal := fun h ↦ hx1 (hxy.trans h)
  by_cases hy2 : f.xmax ≤ ENNReal.ofReal y
  · simp [rightDerivAux, hy1, hy2]
  have hx2 : ¬ f.xmax ≤ ENNReal.ofReal x := fun h ↦ hy2 (h.trans (ENNReal.ofReal_le_ofReal hxy))
  simp only [rightDerivAux, hx1, hy1, hx2, hy2, ↓reduceIte, EReal.coe_le_coe_iff]
  exact f.rightDeriv_mono hxy ((ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top).mpr (not_le.mp hx1))
    (not_le.mp hy2)

/-- The right derivative of `f`, as a monotone right-continuous function `ℝ → EReal`: it is `⊥`
below `f.xmin`, `⊤` from `f.xmax` on, and in between it is the right limit of the right derivative
of `f.realFun` (which is that right derivative itself, except possibly at `f.xmin` where the
right derivative of `f.realFun` can be `-∞`). -/
protected noncomputable def rightDerivStieltjes (f : DivFunction) : ERealStieltjes :=
  f.monotone_rightDerivAux.erealStieltjes

lemma rightDerivStieltjes_apply (f : DivFunction) (x : ℝ) :
    f.rightDerivStieltjes x = Function.rightLim f.rightDerivAux x := rfl

lemma rightDerivStieltjes_of_lt_xmin {x : ℝ} (hx : x < f.xmin.toReal) :
    f.rightDerivStieltjes x = ⊥ := by
  rw [rightDerivStieltjes_apply]
  refine rightLim_eq_of_tendsto ((tendsto_congr' ?_).mpr tendsto_const_nhds)
  filter_upwards [Ioo_mem_nhdsGT hx] with y hy
  simp [rightDerivAux, hy.2.le]

lemma rightDerivStieltjes_of_ge_xmax {x : ℝ} (hx : f.xmax ≤ ENNReal.ofReal x) :
    f.rightDerivStieltjes x = ⊤ := by
  have hx1 : f.xmin.toReal < x := by
    rw [← ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top]
    exact xmin_lt_xmax.trans_le hx
  rw [rightDerivStieltjes_apply]
  refine rightLim_eq_of_tendsto ((tendsto_congr' ?_).mpr tendsto_const_nhds)
  filter_upwards [self_mem_nhdsWithin] with y (hy : x < y)
  simp [rightDerivAux, not_le.mpr (hx1.trans hy), hx.trans (ENNReal.ofReal_le_ofReal hy.le)]

lemma rightDerivStieltjes_of_neg {x : ℝ} (hx : x < 0) :
    f.rightDerivStieltjes x = ⊥ :=
  rightDerivStieltjes_of_lt_xmin (hx.trans_le ENNReal.toReal_nonneg)

lemma eventually_mem_toReal_Ioo {x : ℝ} (hx1 : f.xmin.toReal ≤ x)
    (hx2 : ENNReal.ofReal x < f.xmax) :
    ∀ᶠ y in 𝓝[>] x, y ∈ ENNReal.toReal '' Ioo f.xmin f.xmax := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
    ((ENNReal.continuous_ofReal.tendsto x).eventually (gt_mem_nhds hx2))] with y (hy : x < y) hy2
  exact mem_toReal_Ioo_iff.mpr
    ⟨(ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top).mpr (hx1.trans_lt hy), hy2⟩

lemma rightDerivAux_eventuallyEq {x : ℝ} (hx1 : f.xmin.toReal ≤ x)
    (hx2 : ENNReal.ofReal x < f.xmax) :
    f.rightDerivAux =ᶠ[𝓝[>] x] fun y ↦ (rightDeriv f.realFun y : EReal) := by
  filter_upwards [f.eventually_mem_toReal_Ioo hx1 hx2] with y hy
  obtain ⟨hy1, hy2⟩ := mem_toReal_Ioo_iff.mp hy
  simp [rightDerivAux, not_le.mpr ((ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top).mp hy1),
    not_le.mpr hy2]

lemma tendsto_rightDeriv_realFun_nhdsGT {x : ℝ} (hx1 : f.xmin.toReal ≤ x)
    (hx2 : ENNReal.ofReal x < f.xmax) :
    Tendsto (fun y ↦ (rightDeriv f.realFun y : EReal)) (𝓝[>] x)
      (𝓝 (f.rightDerivStieltjes x)) := by
  rw [rightDerivStieltjes_apply]
  exact (tendsto_congr' (rightDerivAux_eventuallyEq hx1 hx2)).mp
    (f.monotone_rightDerivAux.tendsto_rightLim x)

lemma rightDerivStieltjes_eq_rightLim {x : ℝ} (hx1 : f.xmin.toReal ≤ x)
    (hx2 : ENNReal.ofReal x < f.xmax) :
    f.rightDerivStieltjes x = Function.rightLim (fun y ↦ (rightDeriv f.realFun y : EReal)) x :=
  (rightLim_eq_of_tendsto (f.tendsto_rightDeriv_realFun_nhdsGT hx1 hx2)).symm

lemma rightDerivStieltjes_of_mem_interior {x : ℝ} (hx : f.xmin < ENNReal.ofReal x)
    (hx' : ENNReal.ofReal x < f.xmax) :
    f.rightDerivStieltjes x = rightDeriv f.realFun x := by
  rw [rightDerivStieltjes_eq_rightLim ((ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top).mp hx).le hx']
  exact (continuous_coe_real_ereal.continuousAt.comp_continuousWithinAt
    (f.continuousWithinAt_rightDeriv hx hx')).rightLim_eq

lemma rightDerivStieltjes_ne_top_of_lt_xmax {x : ℝ} (hx : ENNReal.ofReal x < f.xmax) :
    f.rightDerivStieltjes x ≠ ⊤ := by
  by_cases hx1 : x < f.xmin.toReal
  · simp [rightDerivStieltjes_of_lt_xmin hx1]
  push Not at hx1
  obtain ⟨y, hy, hxy⟩ := ((f.eventually_mem_toReal_Ioo hx1 hx).and self_mem_nhdsWithin).exists
  obtain ⟨hy1, hy2⟩ := mem_toReal_Ioo_iff.mp hy
  rw [rightDerivStieltjes_apply]
  refine ne_top_of_le_ne_top ?_ (f.monotone_rightDerivAux.rightLim_le hxy)
  simp [rightDerivAux, not_le.mpr ((ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top).mp hy1),
    not_le.mpr hy2]

lemma rightDerivStieltjes_eq_top_iff {x : ℝ} :
    f.rightDerivStieltjes x = ⊤ ↔ f.xmax ≤ ENNReal.ofReal x :=
  ⟨fun h ↦ not_lt.mp fun hx ↦ rightDerivStieltjes_ne_top_of_lt_xmax hx h,
    rightDerivStieltjes_of_ge_xmax⟩

lemma rightDerivStieltjes_ne_bot_of_xmin_lt {x : ℝ} (hx : f.xmin.toReal < x) :
    f.rightDerivStieltjes x ≠ ⊥ := by
  refine ne_bot_of_le_ne_bot ?_ (f.monotone_rightDerivAux.le_rightLim le_rfl)
  simp only [rightDerivAux, not_le.mpr hx, ↓reduceIte]
  split_ifs <;> simp

/-- `f.rightDerivStieltjes` is `⊥` at `f.xmin` iff the right derivative of `f` tends to `-∞` at
`f.xmin`. -/
lemma rightDerivStieltjes_xmin_eq_bot_iff :
    f.rightDerivStieltjes f.xmin.toReal = ⊥
      ↔ Tendsto (rightDeriv f.realFun) (𝓝[>] f.xmin.toReal) atBot := by
  have h := f.tendsto_rightDeriv_realFun_nhdsGT le_rfl
    (by rw [ENNReal.ofReal_toReal xmin_ne_top]; exact xmin_lt_xmax)
  rw [← EReal.tendsto_coe_nhds_bot_iff]
  exact ⟨fun h_eq ↦ h_eq ▸ h, fun h_bot ↦ tendsto_nhds_unique h h_bot⟩

@[simp]
lemma rightDerivStieltjes_one : f.rightDerivStieltjes 1 = rightDeriv f.realFun 1 :=
  rightDerivStieltjes_of_mem_interior (by simpa using xmin_lt_one) (by simpa using one_lt_xmax)

lemma rightDerivStieltjes_one_nonneg : 0 ≤ f.rightDerivStieltjes 1 := by
  simpa using f.rightDeriv_one_nonneg

@[simp]
lemma toReal_max_xmin : (max f.xmin g.xmin).toReal = max f.xmin.toReal g.xmin.toReal :=
  ENNReal.toReal_max xmin_ne_top xmin_ne_top

lemma realFun_add_eventuallyEq {x : ℝ} (hxf : x ∈ ENNReal.toReal '' Ioo f.xmin f.xmax)
    (hxg : x ∈ ENNReal.toReal '' Ioo g.xmin g.xmax) :
    (f + g).realFun =ᶠ[𝓝 x] fun y ↦ f.realFun y + g.realFun y := by
  filter_upwards [(f.isOpen_toReal_Ioo.inter g.isOpen_toReal_Ioo).mem_nhds ⟨hxf, hxg⟩]
    with y ⟨hyf, hyg⟩
  simp only [realFun, add_apply]
  rw [ENNReal.toReal_add (lt_top_of_mem_Ioo (mem_toReal_Ioo_iff.mp hyf)).ne
    (lt_top_of_mem_Ioo (mem_toReal_Ioo_iff.mp hyg)).ne]

lemma rightDeriv_realFun_add {x : ℝ} (hxf : x ∈ ENNReal.toReal '' Ioo f.xmin f.xmax)
    (hxg : x ∈ ENNReal.toReal '' Ioo g.xmin g.xmax) :
    rightDeriv (f + g).realFun x = rightDeriv f.realFun x + rightDeriv g.realFun x := by
  rw [(realFun_add_eventuallyEq hxf hxg).rightDeriv_eq_nhds]
  exact rightDeriv_add_apply' (f.differentiableWithinAt (mem_toReal_Ioo_iff.mp hxf))
    (g.differentiableWithinAt (mem_toReal_Ioo_iff.mp hxg))

lemma rightDerivStieltjes_add :
    (f + g).rightDerivStieltjes = f.rightDerivStieltjes + g.rightDerivStieltjes := by
  ext x
  by_cases hf_top : f.rightDerivStieltjes x = ⊤
  · rw [ERealStieltjes.add_apply_of_eq_top_left hf_top, rightDerivStieltjes_eq_top_iff, xmax_add]
    exact min_le_of_left_le (rightDerivStieltjes_eq_top_iff.mp hf_top)
  by_cases hg_top : g.rightDerivStieltjes x = ⊤
  · rw [ERealStieltjes.add_apply_of_eq_top_right hg_top, rightDerivStieltjes_eq_top_iff, xmax_add]
    exact min_le_of_right_le (rightDerivStieltjes_eq_top_iff.mp hg_top)
  rw [ERealStieltjes.add_apply_of_ne_top hf_top hg_top]
  have hxf_lt : ENNReal.ofReal x < f.xmax :=
    not_le.mp fun h ↦ hf_top (rightDerivStieltjes_of_ge_xmax h)
  have hxg_lt : ENNReal.ofReal x < g.xmax :=
    not_le.mp fun h ↦ hg_top (rightDerivStieltjes_of_ge_xmax h)
  have hx_lt : ENNReal.ofReal x < (f + g).xmax := by
    rw [xmax_add]
    exact lt_min hxf_lt hxg_lt
  by_cases hxf : x < f.xmin.toReal
  · rw [rightDerivStieltjes_of_lt_xmin hxf, EReal.bot_add, rightDerivStieltjes_of_lt_xmin]
    rw [xmin_add, toReal_max_xmin]
    exact hxf.trans_le (le_max_left _ _)
  by_cases hxg : x < g.xmin.toReal
  · rw [rightDerivStieltjes_of_lt_xmin hxg, EReal.add_bot, rightDerivStieltjes_of_lt_xmin]
    rw [xmin_add, toReal_max_xmin]
    exact hxg.trans_le (le_max_right _ _)
  push Not at hxf hxg
  have hxfg : (f + g).xmin.toReal ≤ x := by
    rw [xmin_add, toReal_max_xmin]
    exact max_le hxf hxg
  have h_add : Tendsto (fun y ↦ (rightDeriv f.realFun y : EReal) + rightDeriv g.realFun y)
      (𝓝[>] x) (𝓝 (f.rightDerivStieltjes x + g.rightDerivStieltjes x)) :=
    (EReal.continuousAt_add (Or.inl hf_top) (Or.inr hg_top)).tendsto.comp
      ((f.tendsto_rightDeriv_realFun_nhdsGT hxf hxf_lt).prodMk_nhds
        (g.tendsto_rightDeriv_realFun_nhdsGT hxg hxg_lt))
  rw [rightDerivStieltjes_apply]
  refine rightLim_eq_of_tendsto ((tendsto_congr' ?_).mpr h_add)
  filter_upwards [rightDerivAux_eventuallyEq hxfg hx_lt, f.eventually_mem_toReal_Ioo hxf hxf_lt,
    g.eventually_mem_toReal_Ioo hxg hxg_lt] with y hy hyf hyg
  simp only [hy, rightDeriv_realFun_add hyf hyg, EReal.coe_add]

lemma rightDerivStieltjes_eq_bot_iff_of_xmin_eq (hxmin : f.xmin = g.xmin)
    (h : Tendsto (rightDeriv f.realFun) (𝓝[>] f.xmin.toReal) atBot
      ↔ Tendsto (rightDeriv g.realFun) (𝓝[>] g.xmin.toReal) atBot) (x : ℝ) :
    f.rightDerivStieltjes x = ⊥ ↔ g.rightDerivStieltjes x = ⊥ := by
  rcases lt_trichotomy x f.xmin.toReal with hx | rfl | hx
  · simp [rightDerivStieltjes_of_lt_xmin hx, rightDerivStieltjes_of_lt_xmin (hxmin ▸ hx)]
  · rw [rightDerivStieltjes_xmin_eq_bot_iff, h, ← rightDerivStieltjes_xmin_eq_bot_iff, hxmin]
  · simp [rightDerivStieltjes_ne_bot_of_xmin_lt hx,
      rightDerivStieltjes_ne_bot_of_xmin_lt (hxmin ▸ hx : g.xmin.toReal < x)]

lemma rightDerivAux_smul {c : ℝ≥0} (hc : c ≠ 0) :
    (c • f).rightDerivAux = fun x ↦ ((c : ℝ) : EReal) * f.rightDerivAux x := by
  ext x
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  simp only [rightDerivAux, xmin_smul hc, xmax_smul hc, realFun_smul, rightDeriv_const_mul]
  split_ifs
  · rw [EReal.coe_mul_bot_of_pos hc']
  · rw [EReal.coe_mul_top_of_pos hc']
  · rw [EReal.coe_mul]

lemma rightDerivStieltjes_smul {c : ℝ≥0} (hc : c ≠ 0) :
    (c • f).rightDerivStieltjes = c • f.rightDerivStieltjes := by
  ext x
  rw [ERealStieltjes.smul_apply, rightDerivStieltjes_apply, rightDerivStieltjes_apply,
    rightDerivAux_smul hc, EReal.coe_nnreal_eq_coe_real]
  exact rightLim_eq_of_tendsto
    ((EReal.continuous_coe_mul.tendsto _).comp (f.monotone_rightDerivAux.tendsto_rightLim x))

end RightDeriv

end DivFunction

end ProbabilityTheory

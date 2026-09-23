/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import TestingLowerBounds.Convex
public import TestingLowerBounds.ForMathlib.ENNReal

/-!
# Divergence functions

A divergence function is a convex and continuous function `f : ℝ≥0∞ → ℝ≥0∞` with `f 1 = 0`.
These are the functions used to define f-divergences.

## Main definitions

* `DivFunction`: the type of divergence functions. It is an `ℝ≥0`-module.
* `DivFunction.xmin`, `DivFunction.xmax`: the endpoints of the effective domain `{x | f x ≠ ∞}`
  of `f`, which is an interval containing `1` in its interior.
* `DivFunction.realFun`: the function `x ↦ (f (ENNReal.ofReal x)).toReal` from `ℝ` to `ℝ`. It is
  convex on `ENNReal.toReal '' Ioo f.xmin f.xmax`.

## Main statements

* `DivFunction.antitoneOn`, `DivFunction.monotoneOn`: a divergence function is nonincreasing on
  `[0, 1]` and nondecreasing on `[1, ∞]`.
* `DivFunction.apply_add_le_apply_add`: `f` lies above its supporting lines at the interior points
  of its effective domain.
* `DivFunction.le_of_forall_rat_tangent_le`: if `g` dominates the supporting lines of `f` at all
  rational interior points, evaluated at `y`, then `f y ≤ g`.

-/

@[expose] public section

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- A divergence function: a convex and continuous function `ℝ≥0∞ → ℝ≥0∞` with value `0` at `1`.
These are the functions used to define f-divergences. -/
structure DivFunction where
  /-- The underlying function `ℝ≥0∞ → ℝ≥0∞`. -/
  toFun : ℝ≥0∞ → ℝ≥0∞
  one : toFun 1 = 0
  convexOn' : ConvexOn ℝ≥0 univ toFun
  -- the continuity everywhere but 0 and ∞ is implied by the convexity
  continuous' : Continuous toFun

namespace DivFunction

attribute [coe] toFun

instance instCoeFun : CoeFun DivFunction fun _ ↦ ℝ≥0∞ → ℝ≥0∞ := ⟨toFun⟩

initialize_simps_projections DivFunction (toFun → apply)

@[ext] lemma ext {f g : DivFunction} (h : ∀ x, f x = g x) : f = g :=
  (DivFunction.mk.injEq ..).mpr (funext h)

section Def
variable (f : DivFunction)

@[simp] lemma apply_one : f 1 = 0 := f.one

lemma convexOn : ConvexOn ℝ≥0 univ f := f.convexOn'

lemma continuous : Continuous f := f.continuous'

lemma measurable : Measurable f := f.continuous.measurable

/-- The real function `x ↦ (f (ENNReal.ofReal x)).toReal` associated with a `DivFunction`. -/
noncomputable def realFun : ℝ → ℝ := fun x ↦ (f (ENNReal.ofReal x)).toReal

end Def

section Monotone
variable (f : DivFunction)

/-- A `DivFunction` is nondecreasing on `[1, ∞]`. -/
lemma monotoneOn : MonotoneOn f (Ici 1) := by
  have key {x y : ℝ≥0∞} (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≠ ∞) : f x ≤ f y := by
    obtain ⟨u, v, huv, hxuv⟩ := ENNReal.exists_nnreal_smul_add_eq hy hx hxy
    calc f x = f (u • 1 + v • y) := by rw [hxuv]
    _ ≤ u • f 1 + v • f y := f.convexOn.2 (mem_univ _) (mem_univ _) zero_le zero_le huv
    _ = v • f y := by simp
    _ ≤ f y := by
      rw [ENNReal.smul_def, smul_eq_mul]
      exact mul_le_of_le_one_left' (ENNReal.coe_le_one_iff.mpr (le_add_self.trans_eq huv))
  intro x hx y _ hxy
  rcases eq_or_ne y ∞ with rfl | hy_top
  · rcases eq_or_lt_of_le hxy with rfl | hx_lt
    · exact le_rfl
    refine (isClosed_le continuous_const f.continuous).closure_subset_iff.mpr
      (fun z (hz : z ∈ Ioo x ∞) ↦ key hx hz.1.le hz.2.ne) ?_
    rw [closure_Ioo hx_lt.ne]
    exact right_mem_Icc.mpr le_top
  · exact key hx hxy hy_top

/-- A `DivFunction` is nonincreasing on `[0, 1]`. -/
lemma antitoneOn : AntitoneOn f (Iic 1) := by
  intro x _ y hy hxy
  obtain ⟨u, v, huv, hyuv⟩ := ENNReal.exists_nnreal_smul_add_eq ENNReal.one_ne_top hxy hy
  calc f y = f (u • x + v • 1) := by rw [hyuv]
  _ ≤ u • f x + v • f 1 := f.convexOn.2 (mem_univ _) (mem_univ _) zero_le zero_le huv
  _ = u • f x := by simp
  _ ≤ f x := by
    rw [ENNReal.smul_def, smul_eq_mul]
    exact mul_le_of_le_one_left' (ENNReal.coe_le_one_iff.mpr ((self_le_add_right u v).trans_eq huv))

lemma apply_eq_zero_of_le_one (h0 : f 0 = 0) {x : ℝ≥0∞} (hx : x ≤ 1) : f x = 0 :=
  le_antisymm ((f.antitoneOn (mem_Iic.2 zero_le_one) (mem_Iic.2 hx) zero_le).trans_eq h0)
    zero_le

end Monotone

section EffectiveDomain
variable {f : DivFunction}

/-- Lower bound of the effective domain of `f`. -/
noncomputable def xmin (f : DivFunction) : ℝ≥0∞ := sInf {x | f x ≠ ∞}
/-- Upper bound of the effective domain of `f`. -/
noncomputable def xmax (f : DivFunction) : ℝ≥0∞ := sSup {x | f x ≠ ∞}

lemma eventually_ne_top_nhds_one (f : DivFunction) : ∀ᶠ a in 𝓝 1, f a ≠ ∞ :=
  f.continuous.continuousAt.eventually_ne (by simp)

lemma xmin_lt_one : f.xmin < 1 := by
  obtain ⟨a, ha_lt, ha⟩ := f.eventually_ne_top_nhds_one.exists_lt
  exact sInf_lt_iff.mpr ⟨a, ha, ha_lt⟩

lemma one_lt_xmax : 1 < f.xmax := by
  obtain ⟨a, ha_gt, ha⟩ := f.eventually_ne_top_nhds_one.exists_gt
  exact lt_sSup_iff.mpr ⟨a, ha, ha_gt⟩

lemma xmin_lt_top : f.xmin < ∞ := lt_top_of_lt xmin_lt_one

lemma xmin_ne_top : f.xmin ≠ ∞ := xmin_lt_top.ne

lemma xmin_toReal_lt_one : f.xmin.toReal < 1 := by
  rw [← ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top, ENNReal.ofReal_one]
  exact xmin_lt_one

lemma xmax_pos : 0 < f.xmax := zero_lt_one.trans one_lt_xmax

lemma xmin_lt_xmax : f.xmin < f.xmax := xmin_lt_one.trans one_lt_xmax

lemma eq_top_of_lt_xmin {x : ℝ≥0∞} (hx : x < f.xmin) : f x = ∞ := by
  by_contra h
  exact hx.not_ge (sInf_le h)

lemma eq_top_of_xmax_lt {x : ℝ≥0∞} (hx : f.xmax < x) : f x = ∞ := by
  by_contra h
  exact hx.not_ge (le_sSup h)

lemma lt_top_of_mem_Ioo {x : ℝ≥0∞} (hx : x ∈ Ioo f.xmin f.xmax) : f x < ∞ := by
  rw [mem_Ioo, xmin, sInf_lt_iff, xmax, lt_sSup_iff] at hx
  obtain ⟨a, ha, hax⟩ := hx.1
  obtain ⟨b, hb, hxb⟩ := hx.2
  rcases le_total x 1 with hx1 | h1x
  · exact (f.antitoneOn (hax.le.trans hx1) hx1 hax.le).trans_lt (Ne.lt_top ha)
  · exact (f.monotoneOn h1x (h1x.trans hxb.le) hxb.le).trans_lt (Ne.lt_top hb)

lemma apply_xmin_eq_top (h : 0 < f.xmin) : f f.xmin = ∞ := by
  refine (isClosed_eq f.continuous continuous_const).closure_subset_iff.mpr
    (fun _ (hx : _ ∈ Iio f.xmin) ↦ eq_top_of_lt_xmin hx) ?_
  rw [closure_Iio' ⟨0, h⟩]
  exact mem_Iic.mpr le_rfl

lemma apply_xmax_eq_top (h : f.xmax ≠ ∞) : f f.xmax = ∞ := by
  refine (isClosed_eq f.continuous continuous_const).closure_subset_iff.mpr
    (fun _ (hx : _ ∈ Ioi f.xmax) ↦ eq_top_of_xmax_lt hx) ?_
  rw [closure_Ioi' ⟨∞, h.lt_top⟩]
  exact mem_Ici.mpr le_rfl

lemma xmin_eq_zero (hf : ∀ x, 0 < x → x ≠ ∞ → f x ≠ ∞) : f.xmin = 0 := by
  refine le_antisymm ?_ zero_le
  refine le_of_forall_gt_imp_ge_of_dense fun x hx ↦ ?_
  by_cases hx_top : x = ∞
  · exact hx_top ▸ le_top
  exact sInf_le (hf x hx hx_top)

lemma xmax_eq_top (hf : ∀ x, 0 < x → x ≠ ∞ → f x ≠ ∞) : f.xmax = ∞ := by
  rw [xmax, sSup_eq_top]
  intro b hb
  refine ⟨b + 1, hf _ (zero_lt_one.trans_le le_add_self)
    (ENNReal.add_ne_top.mpr ⟨hb.ne, ENNReal.one_ne_top⟩), ENNReal.lt_add_right hb.ne one_ne_zero⟩

lemma isOpen_toReal_Ioo (f : DivFunction) : IsOpen (ENNReal.toReal '' Ioo f.xmin f.xmax) := by
  rcases eq_or_ne f.xmax ∞ with h_top | h_top
  · rw [h_top, ENNReal.toReal_image_Ioo_top xmin_ne_top]
    exact isOpen_Ioi
  · rw [ENNReal.toReal_image_Ioo xmin_ne_top h_top]
    exact isOpen_Ioo

lemma convex_toReal_Ioo (f : DivFunction) : Convex ℝ (ENNReal.toReal '' Ioo f.xmin f.xmax) := by
  rcases eq_or_ne f.xmax ∞ with h_top | h_top
  · rw [h_top, ENNReal.toReal_image_Ioo_top xmin_ne_top]
    exact convex_Ioi _
  · rw [ENNReal.toReal_image_Ioo xmin_ne_top h_top]
    exact convex_Ioo _ _

lemma mem_toReal_Ioo_iff {x : ℝ} :
    x ∈ ENNReal.toReal '' Ioo f.xmin f.xmax
      ↔ f.xmin < ENNReal.ofReal x ∧ ENNReal.ofReal x < f.xmax := by
  refine ⟨?_, fun h ↦ ⟨ENNReal.ofReal x, h, ENNReal.toReal_ofReal ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [ENNReal.ofReal_toReal (ne_top_of_lt hy.2)]
  · by_contra hx
    simp [ENNReal.ofReal_of_nonpos (not_le.mp hx).le] at h

end EffectiveDomain

section RealFun
variable (f : DivFunction)

@[simp] lemma realFun_one : f.realFun 1 = 0 := by simp [realFun]

lemma realFun_nonneg {x : ℝ} : 0 ≤ f.realFun x := ENNReal.toReal_nonneg

@[simp] lemma realFun_of_nonpos {x : ℝ} (hx : x ≤ 0) : f.realFun x = f.realFun 0 := by
  simp [realFun, ENNReal.ofReal_of_nonpos hx]

lemma realFun_of_lt_xmin {x : ℝ} (hx : ENNReal.ofReal x < f.xmin) : f.realFun x = 0 := by
  simp [realFun, eq_top_of_lt_xmin hx]

lemma realFun_of_xmax_lt {x : ℝ} (hx : f.xmax < ENNReal.ofReal x) : f.realFun x = 0 := by
  simp [realFun, eq_top_of_xmax_lt hx]

lemma realFun_toReal {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    f.realFun x.toReal = (f x).toReal := by rw [realFun, ENNReal.ofReal_toReal hx]

lemma measurable_realFun : Measurable f.realFun :=
  f.measurable.ennreal_toReal.comp ENNReal.measurable_ofReal

/-- Convexity inequality for `f` at points `ENNReal.ofReal x` and `ENNReal.ofReal y`. -/
private lemma apply_ofReal_add_le {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    f (ENNReal.ofReal (a * x + b * y))
      ≤ ENNReal.ofReal a * f (ENNReal.ofReal x) + ENNReal.ofReal b * f (ENNReal.ofReal y) := by
  have h := f.convexOn.2 (mem_univ (ENNReal.ofReal x)) (mem_univ (ENNReal.ofReal y))
    (zero_le (a := a.toNNReal)) (zero_le (a := b.toNNReal))
    (by rw [← Real.toNNReal_add ha hb, hab, Real.toNNReal_one])
  simp only [ENNReal.smul_def, smul_eq_mul] at h
  rwa [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul ha,
    ENNReal.ofReal_mul hb]

/-- The set of nonnegative reals at which `f` is finite is convex. -/
lemma convex_setOf_ne_top : Convex ℝ {x : ℝ | 0 ≤ x ∧ f (ENNReal.ofReal x) ≠ ∞} := by
  intro x hx y hy a b ha hb hab
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ne_top_of_le_ne_top ?_
    (f.apply_ofReal_add_le hx.1 hy.1 ha hb hab)⟩
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx.2,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy.2⟩

/-- `f.realFun` is convex on the set of nonnegative reals at which `f` is finite. -/
lemma convexOn_realFun_setOf_ne_top :
    ConvexOn ℝ {x : ℝ | 0 ≤ x ∧ f (ENNReal.ofReal x) ≠ ∞} f.realFun := by
  refine ⟨f.convex_setOf_ne_top, fun x ⟨hx, hfx⟩ y ⟨hy, hfy⟩ a b ha hb hab ↦ ?_⟩
  simp only [realFun, smul_eq_mul]
  refine (ENNReal.toReal_mono (by finiteness) (f.apply_ofReal_add_le hx hy ha hb hab)).trans_eq ?_
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

lemma toReal_Ioo_subset_setOf_ne_top :
    ENNReal.toReal '' Ioo f.xmin f.xmax ⊆ {y : ℝ | 0 ≤ y ∧ f (ENNReal.ofReal y) ≠ ∞} := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  rw [ENNReal.ofReal_toReal (ne_top_of_lt hz.2)]
  exact (f.lt_top_of_mem_Ioo hz).ne

lemma convexOn_Ioo_realFun : ConvexOn ℝ (ENNReal.toReal '' Ioo f.xmin f.xmax) f.realFun :=
  f.convexOn_realFun_setOf_ne_top.subset f.toReal_Ioo_subset_setOf_ne_top f.convex_toReal_Ioo

lemma toReal_mem_interior_setOf_ne_top {x : ℝ≥0∞} (hx : x ∈ Ioo f.xmin f.xmax) :
    x.toReal ∈ interior {y : ℝ | 0 ≤ y ∧ f (ENNReal.ofReal y) ≠ ∞} := by
  refine interior_mono f.toReal_Ioo_subset_setOf_ne_top ?_
  rw [f.isOpen_toReal_Ioo.interior_eq]
  exact mem_image_of_mem _ hx

/-- Supporting line inequality for `f`, written without subtraction in `ℝ≥0∞`. -/
lemma apply_add_le_apply_add {x : ℝ≥0∞} (hx : x ∈ Ioo f.xmin f.xmax) {y : ℝ≥0∞} (hy : y ≠ ∞) :
    f x + ENNReal.ofReal (max (rightDeriv f.realFun x.toReal) 0) * y
        + ENNReal.ofReal (max (-rightDeriv f.realFun x.toReal) 0) * x
      ≤ f y + ENNReal.ofReal (max (rightDeriv f.realFun x.toReal) 0) * x
        + ENNReal.ofReal (max (-rightDeriv f.realFun x.toReal) 0) * y := by
  by_cases hfy : f y = ∞
  · simp [hfy]
  have hx_top : x ≠ ∞ := ne_top_of_lt hx.2
  have hfx : f x ≠ ∞ := (f.lt_top_of_mem_Ioo hx).ne
  have h_tangent := f.convexOn_realFun_setOf_ne_top.affine_le_of_mem_interior
    (f.toReal_mem_interior_setOf_ne_top hx) (y := y.toReal)
    ⟨ENNReal.toReal_nonneg, by rwa [ENNReal.ofReal_toReal hy]⟩
  rw [realFun_toReal f hx_top, realFun_toReal f hy] at h_tangent
  set c := rightDeriv f.realFun x.toReal
  have key : c = max c 0 - max (-c) 0 := (max_zero_sub_max_neg_zero_eq_self c).symm
  have e (a u v : ℝ≥0∞) (ha : a ≠ ∞) (hu : u ≠ ∞) (hv : v ≠ ∞) :
      ENNReal.ofReal (a.toReal + max c 0 * u.toReal + max (-c) 0 * v.toReal)
        = a + ENNReal.ofReal (max c 0) * u + ENNReal.ofReal (max (-c) 0) * v := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_mul (le_max_right _ _),
      ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hu, ENNReal.ofReal_toReal hv]
  rw [← e _ _ _ hfx hy hx_top, ← e _ _ _ hfy hx_top hy]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [key] at h_tangent
  linarith

lemma rightDeriv_mono {x y : ℝ} (hxy : x ≤ y)
    (hx : f.xmin < ENNReal.ofReal x) (hy : ENNReal.ofReal y < f.xmax) :
    rightDeriv f.realFun x ≤ rightDeriv f.realFun y := by
  have h := f.convexOn_Ioo_realFun.monotoneOn_rightDeriv
  rw [f.isOpen_toReal_Ioo.interior_eq] at h
  refine h ?_ ?_ hxy
  · exact mem_toReal_Ioo_iff.mpr ⟨hx, (ENNReal.ofReal_le_ofReal hxy).trans_lt hy⟩
  · exact mem_toReal_Ioo_iff.mpr ⟨hx.trans_le (ENNReal.ofReal_le_ofReal hxy), hy⟩

private lemma rightDeriv_realFun_toReal_mono {x y : ℝ≥0∞} (hx : x ∈ Ioo f.xmin f.xmax)
    (hy : y ∈ Ioo f.xmin f.xmax) (hxy : x ≤ y) :
    rightDeriv f.realFun x.toReal ≤ rightDeriv f.realFun y.toReal := by
  refine f.rightDeriv_mono (ENNReal.toReal_mono (ne_top_of_lt hy.2) hxy) ?_ ?_
  · rw [ENNReal.ofReal_toReal (ne_top_of_lt hx.2)]
    exact hx.1
  · rw [ENNReal.ofReal_toReal (ne_top_of_lt hy.2)]
    exact hy.2

/-- Consequence of the supporting line inequality at `x ≤ y`. -/
private lemma apply_le_add_of_le {a x y g : ℝ≥0∞} (hx_top : x ≠ ∞) (hxy : x ≤ y) {c : ℝ}
    (h : a + ENNReal.ofReal (max c 0) * y + ENNReal.ofReal (max (-c) 0) * x
      ≤ g + ENNReal.ofReal (max c 0) * x + ENNReal.ofReal (max (-c) 0) * y) :
    a ≤ g + ENNReal.ofReal (max (-c) 0) * (y - x) := by
  obtain ⟨d, rfl⟩ : ∃ d, y = x + d := ⟨y - x, (add_tsub_cancel_of_le hxy).symm⟩
  rw [ENNReal.add_sub_cancel_left hx_top]
  refine (le_self_add : a ≤ a + ENNReal.ofReal (max c 0) * d).trans
    (ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (max c 0) * x
      + ENNReal.ofReal (max (-c) 0) * x) (by finiteness) ?_)
  convert h using 1 <;> ring

/-- Consequence of the supporting line inequality at `x ≥ y`. -/
private lemma apply_le_add_of_ge {a x y g : ℝ≥0∞} (hy_top : y ≠ ∞) (hyx : y ≤ x) {c : ℝ}
    (h : a + ENNReal.ofReal (max c 0) * y + ENNReal.ofReal (max (-c) 0) * x
      ≤ g + ENNReal.ofReal (max c 0) * x + ENNReal.ofReal (max (-c) 0) * y) :
    a ≤ g + ENNReal.ofReal (max c 0) * (x - y) := by
  obtain ⟨d, rfl⟩ : ∃ d, x = y + d := ⟨x - y, (add_tsub_cancel_of_le hyx).symm⟩
  rw [ENNReal.add_sub_cancel_left hy_top]
  refine (le_self_add : a ≤ a + ENNReal.ofReal (max (-c) 0) * d).trans
    (ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (max c 0) * y
      + ENNReal.ofReal (max (-c) 0) * y) (by finiteness) ?_)
  convert h using 1 <;> ring

/-- If `g` dominates the supporting lines of `f` at all rational interior points, evaluated at
`y`, then `f y ≤ g`. This is the pointwise step of Jensen's inequality for conditional
expectations. -/
lemma le_of_forall_rat_tangent_le {y g : ℝ≥0∞} (hy_top : y ≠ ∞)
    (h : ∀ q : ℚ, ENNReal.ofReal q ∈ Ioo f.xmin f.xmax →
      f (ENNReal.ofReal q)
          + ENNReal.ofReal (max (rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0) * y
          + ENNReal.ofReal (max (-rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0)
            * ENNReal.ofReal q
        ≤ g + ENNReal.ofReal (max (rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0)
            * ENNReal.ofReal q
          + ENNReal.ofReal (max (-rightDeriv f.realFun (ENNReal.ofReal q).toReal) 0) * y) :
    f y ≤ g := by
  have h1 : (1 : ℝ≥0∞) ∈ Ioo f.xmin f.xmax := ⟨xmin_lt_one, one_lt_xmax⟩
  have h_tendsto {q : ℕ → ℚ} {z : ℝ≥0∞} (hz : z ≠ ∞)
      (hq : Tendsto (fun n ↦ (q n : ℝ)) atTop (𝓝 z.toReal)) :
      Tendsto (fun n ↦ ENNReal.ofReal (q n)) atTop (𝓝 z) := by
    rw [← ENNReal.ofReal_toReal hz]
    exact (ENNReal.continuous_ofReal.tendsto _).comp hq
  -- approximate a point `z ≤ y` of the closure of the domain from below by rational points
  have h_below {z a : ℝ≥0∞} (ha : a ∈ Ioo f.xmin f.xmax) (haz : a < z) (hzy : z ≤ y)
      (hz : z ≤ f.xmax) (hz_top : z ≠ ∞) :
      f z ≤ g + ENNReal.ofReal (max (-rightDeriv f.realFun a.toReal) 0) * (y - z) := by
    have ha_top : a ≠ ∞ := ne_top_of_lt ha.2
    obtain ⟨q, -, hq, hq_tendsto⟩ := Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
      Rat.cast_mono (ENNReal.toReal_strict_mono hz_top haz)
    have hq' n : ENNReal.ofReal (q n) ∈ Ioo a z :=
      ⟨(ENNReal.lt_ofReal_iff_toReal_lt ha_top).mpr (hq n).1,
        (ENNReal.ofReal_lt_iff_lt_toReal (ENNReal.toReal_nonneg.trans (hq n).1.le) hz_top).mpr
          (hq n).2⟩
    have hq_mem n : ENNReal.ofReal (q n) ∈ Ioo f.xmin f.xmax :=
      ⟨ha.1.trans (hq' n).1, (hq' n).2.trans_le hz⟩
    have h_lim := h_tendsto hz_top hq_tendsto
    refine le_of_tendsto_of_tendsto' ((f.continuous.tendsto z).comp h_lim)
      (tendsto_const_nhds.add (ENNReal.Tendsto.const_mul
        (ENNReal.Tendsto.sub tendsto_const_nhds h_lim (Or.inl hy_top))
        (Or.inr ENNReal.ofReal_ne_top))) fun n ↦ ?_
    refine (apply_le_add_of_le ENNReal.ofReal_ne_top ((hq' n).2.le.trans hzy)
      (h (q n) (hq_mem n))).trans ?_
    gcongr
    exact f.rightDeriv_realFun_toReal_mono ha (hq_mem n) (hq' n).1.le
  -- approximate a point `z ≥ y` of the closure of the domain from above by rational points
  have h_above {z b : ℝ≥0∞} (hb : b ∈ Ioo f.xmin f.xmax) (hzb : z < b) (hyz : y ≤ z)
      (hz : f.xmin ≤ z) :
      f z ≤ g + ENNReal.ofReal (max (rightDeriv f.realFun b.toReal) 0) * (z - y) := by
    have hb_top : b ≠ ∞ := ne_top_of_lt hb.2
    have hz_top : z ≠ ∞ := ne_top_of_lt hzb
    obtain ⟨q, -, hq, hq_tendsto⟩ := Rat.denseRange_cast.exists_seq_strictAnti_tendsto_of_lt
      Rat.cast_mono (ENNReal.toReal_strict_mono hb_top hzb)
    have hq' n : ENNReal.ofReal (q n) ∈ Ioo z b :=
      ⟨(ENNReal.lt_ofReal_iff_toReal_lt hz_top).mpr (hq n).1,
        (ENNReal.ofReal_lt_iff_lt_toReal (ENNReal.toReal_nonneg.trans (hq n).1.le) hb_top).mpr
          (hq n).2⟩
    have hq_mem n : ENNReal.ofReal (q n) ∈ Ioo f.xmin f.xmax :=
      ⟨hz.trans_lt (hq' n).1, (hq' n).2.trans hb.2⟩
    have h_lim := h_tendsto hz_top hq_tendsto
    refine le_of_tendsto_of_tendsto' ((f.continuous.tendsto z).comp h_lim)
      (tendsto_const_nhds.add (ENNReal.Tendsto.const_mul
        (ENNReal.Tendsto.sub h_lim tendsto_const_nhds (Or.inl hz_top))
        (Or.inr ENNReal.ofReal_ne_top))) fun n ↦ ?_
    refine (apply_le_add_of_ge hy_top (hyz.trans (hq' n).1.le) (h (q n) (hq_mem n))).trans ?_
    gcongr
    exact f.rightDeriv_realFun_toReal_mono (hq_mem n) hb (hq' n).2.le
  -- at an endpoint `z ≠ y` of the domain, `f z = ∞` and the bound forces `g = ∞`
  have of_eq_top {z d : ℝ≥0∞} {K : ℝ} (hz : f z = ∞) (hd : d ≠ ∞)
      (h_le : f z ≤ g + ENNReal.ofReal K * d) : f y ≤ g := by
    rw [hz, top_le_iff, ENNReal.add_eq_top] at h_le
    rcases h_le with hg | hg
    · simp [hg]
    · exact absurd hg (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd)
  rcases le_or_gt y f.xmin with hy_le | hy_gt
  · have h_le := h_above h1 xmin_lt_one hy_le le_rfl
    rcases hy_le.eq_or_lt with rfl | hy_lt
    · simpa using h_le
    · exact of_eq_top (apply_xmin_eq_top (bot_le.trans_lt hy_lt))
        (ENNReal.sub_ne_top xmin_ne_top) h_le
  rcases lt_or_ge y f.xmax with hy_lt | hy_ge
  · obtain ⟨a, ha_gt, ha_lt⟩ := exists_between hy_gt
    simpa using h_below ⟨ha_gt, ha_lt.trans hy_lt⟩ ha_lt le_rfl hy_lt.le hy_top
  · have hmax_top : f.xmax ≠ ∞ := ne_top_of_le_ne_top hy_top hy_ge
    have h_le := h_below h1 one_lt_xmax hy_ge le_rfl hmax_top
    rcases hy_ge.eq_or_lt with rfl | hy_gt'
    · simpa using h_le
    · exact of_eq_top (apply_xmax_eq_top hmax_top) (ENNReal.sub_ne_top hy_top) h_le

lemma differentiableWithinAt {x : ℝ} (hx : ENNReal.ofReal x ∈ Ioo f.xmin f.xmax) :
    DifferentiableWithinAt ℝ f.realFun (Ioi x) x := by
  refine f.convexOn_Ioo_realFun.differentiableWithinAt_Ioi_of_mem_interior ?_
  rw [f.isOpen_toReal_Ioo.interior_eq]
  exact mem_toReal_Ioo_iff.mpr hx

lemma isMinOn_realFun_one {s : Set ℝ} : IsMinOn f.realFun s 1 :=
  fun _ _ ↦ by simp [realFun_nonneg]

lemma one_mem_interior_toReal_Ioo_xmin_xmax :
    1 ∈ interior (ENNReal.toReal '' Ioo f.xmin f.xmax) := by
  rw [f.isOpen_toReal_Ioo.interior_eq]
  exact mem_toReal_Ioo_iff.mpr (by simp [xmin_lt_one, one_lt_xmax])

lemma leftDeriv_one_nonpos : leftDeriv f.realFun 1 ≤ 0 :=
  f.convexOn_Ioo_realFun.leftDeriv_nonpos_of_isMinOn f.isMinOn_realFun_one
    f.one_mem_interior_toReal_Ioo_xmin_xmax

lemma rightDeriv_one_nonneg : 0 ≤ rightDeriv f.realFun 1 :=
  f.convexOn_Ioo_realFun.rightDeriv_nonneg_of_isMinOn f.isMinOn_realFun_one
    f.one_mem_interior_toReal_Ioo_xmin_xmax

lemma continuousOn_realFun_Ioo :
    ContinuousOn f.realFun (ENNReal.toReal '' (Ioo f.xmin f.xmax)) :=
  ConvexOn.continuousOn f.isOpen_toReal_Ioo f.convexOn_Ioo_realFun

/-- If `f.realFun` is strictly convex on a neighborhood of `1`, then `1` is the only zero of `f`. -/
lemma eq_zero_iff {a b : ℝ} (ha : a < 1) (hb : 1 < b)
    (hf_cvx : StrictConvexOn ℝ (Ioo a b) f.realFun) {x : ℝ≥0∞} :
    f x = 0 ↔ x = 1 := by
  have key z (hz : z ∈ Ioo (ENNReal.ofReal a) (ENNReal.ofReal b)) (hfz : f z = 0) : z = 1 := by
    have hz_top : z ≠ ∞ := ne_top_of_lt hz.2
    have h_mem : z.toReal ∈ Ioo a b := by
      refine ⟨(ENNReal.ofReal_lt_ofReal_iff'.mp ?_).1,
        (ENNReal.lt_ofReal_iff_toReal_lt hz_top).mp hz.2⟩
      rw [ENNReal.ofReal_toReal hz_top]
      exact hz.1
    have h_min : IsMinOn f.realFun (Ioo a b) z.toReal :=
      fun _ _ ↦ by simp [realFun_toReal f hz_top, hfz, realFun_nonneg]
    rw [← ENNReal.ofReal_toReal hz_top,
      hf_cvx.eq_of_isMinOn h_min f.isMinOn_realFun_one h_mem ⟨ha, hb⟩, ENNReal.ofReal_one]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rcases lt_trichotomy x 1 with hx1 | rfl | h1x
  · obtain ⟨z, hxz, hz1⟩ := exists_between (max_lt hx1 (ENNReal.ofReal_lt_one.mpr ha))
    have hfz : f z = 0 := le_antisymm
      ((f.antitoneOn ((le_max_left _ _).trans hxz.le |>.trans hz1.le) hz1.le
        ((le_max_left _ _).trans hxz.le)).trans_eq h) zero_le
    exact absurd (key z ⟨(le_max_right _ _).trans_lt hxz,
      hz1.trans (ENNReal.one_lt_ofReal.mpr hb)⟩ hfz) hz1.ne
  · rfl
  · obtain ⟨z, h1z, hzx⟩ := exists_between (lt_min h1x (ENNReal.one_lt_ofReal.mpr hb))
    have hfz : f z = 0 := le_antisymm
      ((f.monotoneOn h1z.le (h1z.le.trans (hzx.le.trans (min_le_left _ _)))
        (hzx.le.trans (min_le_left _ _))).trans_eq h) zero_le
    exact absurd (key z ⟨(ENNReal.ofReal_lt_one.mpr ha).trans h1z,
      hzx.trans_le (min_le_right _ _)⟩ hfz) h1z.ne'

end RealFun

variable {f g : DivFunction}

section Module

/-- The zero divergence function. -/
protected def zero : DivFunction where
  toFun := 0
  one := rfl
  convexOn' := convexOn_const _ convex_univ
  continuous' := continuous_const

/-- Sum of two divergence functions. -/
protected noncomputable def add (f g : DivFunction) : DivFunction where
  toFun := fun x ↦ f x + g x
  one := by simp
  convexOn' := f.convexOn.add g.convexOn
  continuous' := f.continuous.add g.continuous

noncomputable
instance : AddZeroClass DivFunction where
  add := DivFunction.add
  zero := DivFunction.zero
  zero_add _ := ext fun _ ↦ zero_add _
  add_zero _ := ext fun _ ↦ add_zero _

@[simp] lemma zero_apply (x : ℝ≥0∞) : (0 : DivFunction) x = 0 := rfl

@[simp] lemma add_apply (f g : DivFunction) (x : ℝ≥0∞) : (f + g) x = f x + g x := rfl

noncomputable
instance : AddCommMonoid DivFunction where
  nsmul n f := nsmulRec n f
  add_assoc _ _ _ := ext fun _ ↦ add_assoc _ _ _
  add_comm _ _ := ext fun _ ↦ add_comm _ _
  __ := DivFunction.instAddZeroClass

noncomputable
instance : SMul ℝ≥0 DivFunction where
  smul c f := {
    toFun := fun x ↦ c * f x
    one := by simp
    convexOn' := ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ by
      have h := f.convexOn.2 (mem_univ x) (mem_univ y) ha hb hab
      calc (c : ℝ≥0∞) * f (a • x + b • y)
        _ ≤ (c : ℝ≥0∞) * (a • f x + b • f y) := by gcongr
        _ = a • ((c : ℝ≥0∞) * f x) + b • ((c : ℝ≥0∞) * f y) := by
            simp only [ENNReal.smul_def, smul_eq_mul]; ring⟩
    continuous' := (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp f.continuous}

@[simp] lemma smul_apply (c : ℝ≥0) (f : DivFunction) (x : ℝ≥0∞) : (c • f) x = c * f x := rfl

noncomputable
instance : Module ℝ≥0 DivFunction where
  one_smul _ := ext fun _ ↦ one_mul _
  mul_smul _ _ _ := ext fun _ ↦ by simp [mul_assoc]
  smul_zero _ := ext fun _ ↦ mul_zero _
  smul_add _ _ _ := ext fun _ ↦ mul_add _ _ _
  add_smul _ _ _ := ext fun _ ↦ by simp [add_mul]
  zero_smul _ := ext fun _ ↦ zero_mul _

end Module

@[simp] lemma realFun_zero : (0 : DivFunction).realFun = fun _ ↦ 0 := by
  unfold DivFunction.realFun
  simp

lemma realFun_smul (c : ℝ≥0) (f : DivFunction) : (c • f).realFun = fun x ↦ c * f.realFun x := by
  ext x
  simp [realFun, ENNReal.toReal_mul]

@[simp] lemma xmin_zero : (0 : DivFunction).xmin = 0 := by simp [xmin]

@[simp] lemma xmax_zero : (0 : DivFunction).xmax = ∞ := by simp [xmax]

@[simp] lemma xmin_add : (f + g).xmin = max f.xmin g.xmin := by
  simp only [xmin, add_apply, ne_eq, ENNReal.add_eq_top, not_or]
  refine le_antisymm ?_ (max_le (sInf_le_sInf fun _ hx ↦ hx.1) (sInf_le_sInf fun _ hx ↦ hx.2))
  refine le_of_forall_gt_imp_ge_of_dense fun y hy ↦ ?_
  rw [max_lt_iff, sInf_lt_iff, sInf_lt_iff] at hy
  obtain ⟨⟨a, ha, hay⟩, ⟨b, hb, hby⟩⟩ := hy
  rcases lt_or_ge 1 y with hy1 | hy1
  · exact (sInf_le (a := 1) (by simp)).trans hy1.le
  have hmax : max a b ≤ 1 := (max_lt hay hby).le.trans hy1
  refine sInf_le_of_le (b := max a b) ⟨?_, ?_⟩ (max_lt hay hby).le
  · exact ne_top_of_le_ne_top ha
      (f.antitoneOn ((le_max_left a b).trans hmax) hmax (le_max_left _ _))
  · exact ne_top_of_le_ne_top hb
      (g.antitoneOn ((le_max_right a b).trans hmax) hmax (le_max_right _ _))

@[simp] lemma xmax_add : (f + g).xmax = min f.xmax g.xmax := by
  simp only [xmax, add_apply, ne_eq, ENNReal.add_eq_top, not_or]
  refine le_antisymm (le_min (sSup_le_sSup fun _ hx ↦ hx.1) (sSup_le_sSup fun _ hx ↦ hx.2)) ?_
  refine le_of_forall_lt fun y hy ↦ ?_
  rw [lt_min_iff, lt_sSup_iff, lt_sSup_iff] at hy
  obtain ⟨⟨a, ha, hya⟩, ⟨b, hb, hyb⟩⟩ := hy
  rw [lt_sSup_iff]
  rcases lt_or_ge y 1 with hy1 | hy1
  · exact ⟨1, by simp, hy1⟩
  refine ⟨min a b, ⟨?_, ?_⟩, lt_min hya hyb⟩
  · exact ne_top_of_le_ne_top ha
      (f.monotoneOn (hy1.trans (lt_min hya hyb).le) (hy1.trans hya.le) (min_le_left _ _))
  · exact ne_top_of_le_ne_top hb
      (g.monotoneOn (hy1.trans (lt_min hya hyb).le) (hy1.trans hyb.le) (min_le_right _ _))

@[simp] lemma xmin_smul {c : ℝ≥0} (hc : c ≠ 0) : (c • f).xmin = f.xmin := by
  simp [xmin, hc, ENNReal.mul_eq_top]

@[simp] lemma xmax_smul {c : ℝ≥0} (hc : c ≠ 0) : (c • f).xmax = f.xmax := by
  simp [xmax, hc, ENNReal.mul_eq_top]

end DivFunction

variable {f : DivFunction}

lemma measurable_divFunction_rnDeriv : Measurable (fun x ↦ f (μ.rnDeriv ν x)) :=
  f.measurable.comp (μ.measurable_rnDeriv ν)

lemma integrable_realFun {g : α → ℝ≥0∞} (hg : AEMeasurable g ν) (hg_lt : ∀ᵐ x ∂ν, g x < ∞)
    (h_int : ∫⁻ x, f (g x) ∂ν ≠ ∞) :
    Integrable (fun x ↦ f.realFun (g x).toReal) ν := by
  have h_eq : (fun x ↦ f (ENNReal.ofReal (g x).toReal)) =ᵐ[ν] fun x ↦ f (g x) := by
    filter_upwards [hg_lt] with x hx
    rw [ENNReal.ofReal_toReal hx.ne]
  refine integrable_toReal_of_lintegral_ne_top
    (f.measurable.comp_aemeasurable hg.ennreal_toReal.ennreal_ofReal) ?_
  rwa [lintegral_congr_ae h_eq]

lemma integral_realFun {g : α → ℝ≥0∞} (hg : AEMeasurable g ν) (hg_lt : ∀ᵐ x ∂ν, g x < ∞)
    (h_int : ∫⁻ x, f (g x) ∂ν ≠ ∞) :
    ∫ x, f.realFun (g x).toReal ∂ν = (∫⁻ x, f (g x) ∂ν).toReal := by
  have h_eq : (fun x ↦ f (ENNReal.ofReal (g x).toReal)) =ᵐ[ν] fun x ↦ f (g x) := by
    filter_upwards [hg_lt] with x hx
    rw [ENNReal.ofReal_toReal hx.ne]
  rw [← lintegral_congr_ae h_eq]
  refine integral_toReal (f.measurable.comp_aemeasurable hg.ennreal_toReal.ennreal_ofReal) ?_
  filter_upwards [h_eq, ae_lt_top' (f.measurable.comp_aemeasurable hg) h_int] with x hx hx'
  rwa [hx]

lemma ofReal_integral_realFun {g : α → ℝ≥0∞} (hg : AEMeasurable g ν) (hg_lt : ∀ᵐ x ∂ν, g x < ∞)
    (h_int : ∫⁻ x, f (g x) ∂ν ≠ ∞) :
    ENNReal.ofReal (∫ x, f.realFun (g x).toReal ∂ν) = ∫⁻ x, f (g x) ∂ν := by
  rw [integral_realFun hg hg_lt h_int, ENNReal.ofReal_toReal h_int]

lemma lintegral_eq_top_of_not_integrable_realFun [SigmaFinite μ]
    (h_int : ¬ Integrable (fun x ↦ f.realFun (μ.rnDeriv ν x).toReal) ν) :
    ∫⁻ x, f (μ.rnDeriv ν x) ∂ν = ∞ := by
  by_contra h
  exact h_int (integrable_realFun (μ.measurable_rnDeriv ν).aemeasurable (μ.rnDeriv_lt_top ν) h)

end ProbabilityTheory

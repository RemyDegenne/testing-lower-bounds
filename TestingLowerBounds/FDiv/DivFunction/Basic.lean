/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import TestingLowerBounds.Convex
import TestingLowerBounds.DerivAtTop
import TestingLowerBounds.FDiv.ERealStieltjes
import TestingLowerBounds.ForMathlib.RnDeriv

/-!

# f-Divergences functions

-/

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

lemma ENNReal.tendsto_of_monotone {ι : Type*} [Preorder ι] {f : ι → ℝ≥0∞} (hf : Monotone f) :
    ∃ y, Tendsto f atTop (𝓝 y) :=
  ⟨_, tendsto_atTop_ciSup hf (OrderTop.bddAbove _)⟩

lemma ENNReal.tendsto_of_monotoneOn {ι : Type*} [SemilatticeSup ι] [Nonempty ι] {x : ι}
    {f : ι → ℝ≥0∞} (hf : MonotoneOn f (Ici x)) :
    ∃ y, Tendsto f atTop (𝓝 y) := by
  classical
  suffices ∃ y, Tendsto (fun z ↦ if x ≤ z then f z else f x) atTop (𝓝 y) by
    obtain ⟨y, hy⟩ := this
    refine ⟨y, ?_⟩
    refine (tendsto_congr' ?_).mp hy
    rw [EventuallyEq, eventually_atTop]
    exact ⟨x, fun z hz ↦ ite_eq_left hz⟩
  refine ENNReal.tendsto_of_monotone (fun y z hyz ↦ ?_)
  split_ifs with hxy hxz hxz
  · exact hf hxy hxz hyz
  · exact absurd (hxy.trans hyz) hxz
  · exact hf le_rfl hxz hxz
  · exact le_rfl

lemma ENNReal.toReal_Ioo {x y : ℝ≥0∞} (hx : x ≠ ∞) (hy : y ≠ ∞) :
    ENNReal.toReal '' (Ioo x y) = Ioo x.toReal y.toReal := by
  ext a
  refine
    ⟨fun ⟨a', ⟨hxa, hay⟩, ha⟩ ↦ ha ▸ ⟨toReal_strict_mono hay.ne_top hxa, toReal_strict_mono hy hay⟩,
    fun ⟨hxa, hay⟩ ↦ ⟨.ofReal a, ⟨?_, ?_⟩, toReal_ofReal (toReal_nonneg.trans_lt hxa).le⟩⟩
  · rw [← ofReal_toReal hx, ofReal_lt_ofReal_iff']
    exact ⟨hxa, toReal_nonneg.trans_lt hxa⟩
  · rw [← ofReal_toReal hy, ofReal_lt_ofReal_iff']
    exact ⟨hay, (toReal_nonneg.trans_lt hxa).trans hay⟩

@[simp]
lemma ENNReal.toReal_Ioo_top {x : ℝ≥0∞} (hx : x ≠ ∞) :
    ENNReal.toReal '' (Ioo x ∞) = Ioi x.toReal := by
  ext a
  refine ⟨fun ⟨a', ⟨hxa, hay⟩, ha⟩ ↦ ha ▸ toReal_strict_mono hay.ne_top hxa,
    fun hxa ↦ ⟨.ofReal a, ⟨?_, ofReal_lt_top⟩, toReal_ofReal (toReal_nonneg.trans_lt hxa).le⟩⟩
  rw [← ofReal_toReal hx, ofReal_lt_ofReal_iff']
  exact ⟨hxa, toReal_nonneg.trans_lt hxa⟩

/-- A point of `[x, y]` (with `y ≠ ∞`) is a convex combination of `x` and `y` with `ℝ≥0` weights. -/
lemma ENNReal.exists_nnreal_smul_add_eq {x y z : ℝ≥0∞} (hy : y ≠ ∞) (hxz : x ≤ z) (hzy : z ≤ y) :
    ∃ u v : ℝ≥0, u + v = 1 ∧ u • x + v • y = z := by
  have hz : z ≠ ∞ := ne_top_of_le_ne_top hy hzy
  have hx : x ≠ ∞ := ne_top_of_le_ne_top hz hxz
  rcases eq_or_lt_of_le (hxz.trans hzy) with hxy | hxy
  · subst hxy
    obtain rfl := le_antisymm hxz hzy
    exact ⟨1, 0, by simp, by simp⟩
  have hxy' : x.toReal < y.toReal := ENNReal.toReal_strict_mono hy hxy
  have hxy_ne : y.toReal - x.toReal ≠ 0 := (sub_pos.mpr hxy').ne'
  set v : ℝ := (z.toReal - x.toReal) / (y.toReal - x.toReal) with hv
  have hv0 : 0 ≤ v :=
    div_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono hz hxz)) (sub_nonneg.mpr hxy'.le)
  have hv1 : v ≤ 1 :=
    (div_le_one (sub_pos.mpr hxy')).mpr (sub_le_sub_right (ENNReal.toReal_mono hy hzy) _)
  refine ⟨(1 - v).toNNReal, v.toNNReal, ?_, ?_⟩
  · rw [← Real.toNNReal_add (sub_nonneg.mpr hv1) hv0, sub_add_cancel, Real.toNNReal_one]
  · rw [← ENNReal.toReal_eq_toReal_iff' ?_ hz]
    · simp only [ENNReal.smul_def, smul_eq_mul,
        ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hx)
          (ENNReal.mul_ne_top ENNReal.coe_ne_top hy),
        ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal _ (sub_nonneg.mpr hv1),
        Real.coe_toNNReal _ hv0]
      rw [hv]
      field_simp
      ring
    · exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hx,
        ENNReal.mul_ne_top ENNReal.coe_ne_top hy⟩

lemma leftDeriv_congr {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝[<] x] g) (hx : f x = g x) :
    leftDeriv f x = leftDeriv g x := h.derivWithin_eq hx

lemma rightDeriv_congr {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝[>] x] g) (hx : f x = g x) :
    rightDeriv f x = rightDeriv g x := h.derivWithin_eq hx

@[simp] lemma leftLim_const {β : Type*} {a : ℝ} {x : β} [TopologicalSpace β] [T2Space β] :
    Function.leftLim (fun _ ↦ x) a = x :=
  leftLim_eq_of_tendsto tendsto_const_nhds

@[simp] lemma rightLim_const {β : Type*} {a : ℝ} {x : β} [TopologicalSpace β] [T2Space β] :
    Function.rightLim (fun _ ↦ x) a = x :=
  rightLim_eq_of_tendsto tendsto_const_nhds

lemma right_continuous_rightLim {β : Type*} [TopologicalSpace β]
    [ConditionallyCompleteLinearOrder β] [OrderTopology β] [T2Space β]
    {f : ℝ → β} (hf : Monotone f)
    {a : ℝ} (h_ne_bot : 𝓝[>] a ≠ ⊥) {y : β} (h_tendsto : Tendsto f (𝓝[>] a) (𝓝 y)) :
    ContinuousWithinAt (Function.rightLim f) (Ici a) a := by
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt,
    rightLim_eq_of_tendsto (h := ⟨h_ne_bot⟩) h_tendsto]
  obtain ⟨u, _, _, _⟩ := exists_seq_strictAnti_tendsto a
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (h := fun x ↦ f (a + 2 * |x - a|))
    h_tendsto ?_ (.of_forall fun _ ↦ hf.le_rightLim le_rfl) ?_
  · refine h_tendsto.comp ?_
    rw [tendsto_nhdsWithin_iff]
    constructor
    · refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      convert (tendsto_const_nhds (x := a)).add ((tendsto_norm_sub_self a).const_mul 2) using 2
      simp
    · refine eventually_nhdsWithin_of_forall fun x hx ↦ ?_
      simp [sub_ne_zero, (mem_Ioi.mp hx).ne']
  · filter_upwards [eventually_nhdsWithin_of_forall fun y hy ↦ hy] with b hb
    refine hf.rightLim_le ?_
    rw [abs_of_nonneg (sub_nonneg.mpr hb.le)]
    calc b = a + (b - a) := by abel
    _ < a + 2 * (b - a) := by
      gcongr
      refine lt_two_mul_self ?_
      exact sub_pos.mpr hb

lemma rightLim_rightLim_of_tendsto {β : Type*}
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] [T2Space β]
    {f : ℝ → β} (hf : Monotone f)
    {a : ℝ} (h_ne_bot : 𝓝[>] a ≠ ⊥) {y : β} (h_tendsto : Tendsto f (𝓝[>] a) (𝓝 y)) :
    Function.rightLim (Function.rightLim f) a = y := by
  rw [← rightLim_eq_of_tendsto (h := ⟨h_ne_bot⟩) h_tendsto,
    ← hf.rightLim.continuousWithinAt_Ioi_iff_rightLim_eq, continuousWithinAt_Ioi_iff_Ici]
  exact right_continuous_rightLim hf h_ne_bot h_tendsto

namespace ConvexOn

lemma nonneg_of_todo {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hf_one : f 1 = 0) (hf_deriv : rightDeriv f 1 = 0) {x : ℝ} (hx : 0 < x) :
    0 ≤ f x := by
  calc 0
  _ = rightDeriv f 1 * x + (f 1 - rightDeriv f 1 * 1) := by simp [hf_one, hf_deriv]
  _ ≤ f x := hf.affine_le_of_mem_interior
    ((interior_Ioi (a := (0 : ℝ))).symm ▸ mem_Ioi.mpr zero_lt_one) hx

lemma nonneg_of_todo' {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hf_one : f 1 = 0) (hf_ld : leftDeriv f 1 ≤ 0) (hf_rd : 0 ≤ rightDeriv f 1)
    {x : ℝ} (hx : 0 < x) :
    0 ≤ f x := by
  rcases le_total x 1 with hx1 | h1x
  · calc 0
    _ ≤ leftDeriv f 1 * x + (f 1 - leftDeriv f 1 * 1) := by
      simp [hf_one, hf_ld, le_mul_of_le_one_right, hx1]
    _ ≤ f x := hf.affine_le_of_mem_interior'
      ((interior_Ioi (a := (0 : ℝ))).symm ▸ mem_Ioi.mpr zero_lt_one) hx
  · calc 0
    _ ≤ rightDeriv f 1 * x + (f 1 - rightDeriv f 1 * 1) := by
      simp [hf_one, hf_rd, le_mul_of_one_le_right, h1x]
    _ ≤ f x := hf.affine_le_of_mem_interior
      ((interior_Ioi (a := (0 : ℝ))).symm ▸ mem_Ioi.mpr zero_lt_one) hx

lemma leftDeriv_nonpos_of_isMinOn {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) {x₀ : ℝ}
    (hf_one : IsMinOn f s x₀) (h_mem : x₀ ∈ interior s) :
    leftDeriv f x₀ ≤ 0 := by
  rw [leftDeriv_def, leftDeriv_eq_sSup_slope_of_mem_interior hf h_mem]
  refine csSup_le ?_ fun a ⟨x, ⟨hxs, hxx₀⟩, hax⟩ ↦ ?_
  · obtain ⟨x, hxx₀, hxs⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp <|
      mem_nhdsWithin_of_mem_nhds <| mem_interior_iff_mem_nhds.mp h_mem
    exact Nonempty.image _ ⟨x, hxs <| mem_Icc.mpr ⟨le_rfl, hxx₀.le⟩, hxx₀⟩
  · rw [← hax, slope, vsub_eq_sub, smul_eq_mul, mul_comm, ← division_def, div_nonpos_iff]
    exact Or.inl ⟨sub_nonneg.mpr <| hf_one hxs, sub_nonpos.mpr hxx₀.le⟩

lemma rightDeriv_nonneg_of_isMinOn {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) {x₀ : ℝ}
    (hf_one : IsMinOn f s x₀) (h_mem : x₀ ∈ interior s) :
    0 ≤ rightDeriv f x₀ := by
  rw [rightDeriv_def, rightDeriv_eq_sInf_slope_of_mem_interior hf h_mem]
  refine le_csInf ?_ fun a ⟨x, ⟨hxs, hxx₀⟩, hax⟩ ↦ ?_
  · obtain ⟨x, hxx₀, hxs⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp <|
      mem_nhdsWithin_of_mem_nhds <| mem_interior_iff_mem_nhds.mp h_mem
    exact Nonempty.image _ ⟨x, hxs <| mem_Icc.mpr ⟨hxx₀.le, le_rfl⟩, hxx₀⟩
  · rw [← hax, slope, vsub_eq_sub, smul_eq_mul, mul_comm, ← division_def, div_nonneg_iff]
    exact Or.inl ⟨sub_nonneg.mpr <| hf_one hxs, sub_nonneg.mpr hxx₀.le⟩

end ConvexOn

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

structure DivFunction where
  toFun : ℝ≥0∞ → ℝ≥0∞
  one : toFun 1 = 0
  convexOn' : ConvexOn ℝ≥0 univ toFun
  -- the continuity everywhere but 0 and ∞ is implied by the convexity
  continuous' : Continuous toFun

namespace DivFunction

attribute [coe] toFun

instance instCoeFun : CoeFun DivFunction fun _ ↦ ℝ≥0∞ → ℝ≥0∞ := ⟨toFun⟩

initialize_simps_projections DivFunction (toFun → apply)

@[ext] lemma ext {f g : DivFunction} (h : ∀ x, f x = g x) : f = g := by
  exact (DivFunction.mk.injEq ..).mpr (funext h)

section Def
variable (f : DivFunction)

@[simp] lemma apply_one : f 1 = 0 := f.one

lemma convexOn : ConvexOn ℝ≥0 univ f := f.convexOn'

lemma continuous : Continuous f := f.continuous'

lemma measurable : Measurable f := f.continuous.measurable

noncomputable
def realFun (f : DivFunction) : ℝ → ℝ := (fun x : ℝ ↦ (f (ENNReal.ofReal x)).toReal)

end Def

section Monotone
variable (f : DivFunction)

lemma le_of_one_le_of_le_of_ne_top {x y : ℝ≥0∞} (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≠ ∞) :
    f x ≤ f y := by
  obtain ⟨u, v, huv, hxuv⟩ := ENNReal.exists_nnreal_smul_add_eq hy hx hxy
  calc f x = f (u • 1 + v • y) := by rw [hxuv]
  _ ≤ u • f 1 + v • f y := f.convexOn.2 (mem_univ _) (mem_univ _) zero_le zero_le huv
  _ = v • f y := by simp
  _ ≤ f y := by
    rw [ENNReal.smul_def, smul_eq_mul]
    exact mul_le_of_le_one_left' (ENNReal.coe_le_one_iff.mpr (le_add_self.trans_eq huv))

/-- A `DivFunction` is nondecreasing on `[1, ∞]`. -/
lemma monotoneOn : MonotoneOn f (Ici 1) := by
  intro x hx y _ hxy
  by_cases hy_top : y = ∞
  swap; · exact f.le_of_one_le_of_le_of_ne_top hx hxy hy_top
  subst hy_top
  rcases eq_or_lt_of_le hxy with rfl | hx_lt
  · exact le_rfl
  have h_ne_bot : (𝓝[<] (∞ : ℝ≥0∞)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Iio' ⟨0, ENNReal.zero_lt_top⟩]
    simp
  refine ge_of_tendsto ((f.continuous.tendsto ∞).mono_left (nhdsWithin_le_nhds (s := Iio ∞))) ?_
  filter_upwards [Ioo_mem_nhdsLT hx_lt] with z hz
  exact f.le_of_one_le_of_le_of_ne_top hx hz.1.le hz.2.ne

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

end Monotone

section EffectiveDomain
variable {f : DivFunction}

lemma eventually_ne_top_nhds_one (f : DivFunction) : ∀ᶠ a in 𝓝 1, f a ≠ ∞ := by
  suffices ∀ᶠ a in 𝓝 1, f a < 1 by
    filter_upwards [this] with x hx using ne_top_of_lt hx
  refine Filter.Tendsto.eventually_lt_const ?_ (f.continuous.tendsto 1)
  simp

/-- Lower bound of the effective domain of `f`. -/
noncomputable def xmin (f : DivFunction) : ℝ≥0∞ := sInf {x | f x ≠ ∞}
/-- Upper bound of the effective domain of `f`. -/
noncomputable def xmax (f : DivFunction) : ℝ≥0∞ := sSup {x | f x ≠ ∞}

lemma xmin_lt_one : f.xmin < 1 := by
  rw [xmin, sInf_lt_iff]
  suffices ∀ᶠ a in 𝓝 1, f a ≠ ⊤ by
    obtain ⟨a, ha_lt, ha⟩ := this.exists_lt
    exact ⟨a, ha, ha_lt⟩
  suffices ∀ᶠ a in 𝓝 1, f a < 1 by
    filter_upwards [this] with x hx using ne_top_of_lt hx
  refine Filter.Tendsto.eventually_lt_const ?_ (f.continuous.tendsto 1)
  simp

lemma xmin_lt_top : f.xmin < ∞ := lt_top_of_lt xmin_lt_one

lemma xmin_ne_top : f.xmin ≠ ∞ := xmin_lt_top.ne

lemma one_lt_xmax : 1 < f.xmax := by
  rw [xmax, lt_sSup_iff]
  obtain ⟨a, ha_gt, ha⟩ := f.eventually_ne_top_nhds_one.exists_gt
  exact ⟨a, ha, ha_gt⟩

lemma xmax_pos : 0 < f.xmax := zero_lt_one.trans one_lt_xmax

lemma xmin_lt_xmax : f.xmin < f.xmax := xmin_lt_one.trans one_lt_xmax

lemma eq_top_of_lt_xmin {x : ℝ≥0∞} (hx_lt : x < f.xmin) : f x = ∞ := by
  rw [xmin] at hx_lt
  by_contra h_eq
  exact not_le_of_gt hx_lt (sInf_le h_eq)

lemma eq_top_of_xmax_lt {x : ℝ≥0∞} (hx_gt : f.xmax < x) : f x = ∞ := by
  rw [xmax] at hx_gt
  by_contra h_eq
  exact not_le_of_gt hx_gt (le_sSup h_eq)

lemma lt_top_of_mem_Ioo {x : ℝ≥0∞} (hx : x ∈ Ioo f.xmin f.xmax) : f x < ∞ := by
  rw [mem_Ioo, xmin, sInf_lt_iff, xmax, lt_sSup_iff] at hx
  obtain ⟨a, ha, hax⟩ := hx.1
  obtain ⟨b, hb, hxb⟩ := hx.2
  rcases le_total x 1 with hx1 | h1x
  · exact (f.antitoneOn (hax.le.trans hx1) hx1 hax.le).trans_lt (Ne.lt_top ha)
  · exact (f.monotoneOn h1x (h1x.trans hxb.le) hxb.le).trans_lt (Ne.lt_top hb)

lemma apply_xmin_eq_top (h : 0 < f.xmin) : f f.xmin = ∞ := by
  suffices Tendsto f (𝓝[<] f.xmin) (𝓝 ∞) by
    have h_ne_bot : (𝓝[<] f.xmin).NeBot := by
      refine mem_closure_iff_nhdsWithin_neBot.mp ?_
      rw [closure_Iio']
      · simp
      · exact ⟨0, h⟩
    refine tendsto_nhds_unique ?_ this
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    exact f.continuous.tendsto _
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  exact eventually_nhdsWithin_of_forall fun x hx ↦ (eq_top_of_lt_xmin hx).symm

lemma apply_xmax_eq_top (h : f.xmax ≠ ∞) : f f.xmax = ∞ := by
  suffices Tendsto f (𝓝[>] f.xmax) (𝓝 ∞) by
    have h_ne_bot : (𝓝[>] f.xmax).NeBot := by
      refine mem_closure_iff_nhdsWithin_neBot.mp ?_
      rw [closure_Ioi']
      · simp
      · exact ⟨⊤, h.lt_top⟩
    refine tendsto_nhds_unique ?_ this
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    exact f.continuous.tendsto _
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  exact eventually_nhdsWithin_of_forall fun x hx ↦ (eq_top_of_xmax_lt hx).symm

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

lemma stronglyMeasurable_realFun : StronglyMeasurable f.realFun :=
  f.measurable_realFun.stronglyMeasurable

/-- `f.realFun` is convex on any convex set of nonnegative reals on which `f` is finite. -/
lemma convexOn_realFun_of_ne_top {s : Set ℝ} (hs : Convex ℝ s) (hs_nonneg : ∀ x ∈ s, 0 ≤ x)
    (h : ∀ x ∈ s, f (ENNReal.ofReal x) ≠ ∞) :
    ConvexOn ℝ s f.realFun := by
  refine ⟨hs, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have hx0 := hs_nonneg x hx
  have hy0 := hs_nonneg y hy
  have hfx : f (ENNReal.ofReal x) ≠ ∞ := h x hx
  have hfy : f (ENNReal.ofReal y) ≠ ∞ := h y hy
  have h_eq : ENNReal.ofReal (a * x + b * y)
      = ↑a.toNNReal * ENNReal.ofReal x + ↑b.toNNReal * ENNReal.ofReal y := by
    rw [ENNReal.ofReal_add (mul_nonneg ha hx0) (mul_nonneg hb hy0), ENNReal.ofReal_mul ha,
      ENNReal.ofReal_mul hb]
    rfl
  have hab' : a.toNNReal + b.toNNReal = 1 := by
    rw [← Real.toNNReal_add ha hb, hab, Real.toNNReal_one]
  have h_cvx := f.convexOn.2 (mem_univ (ENNReal.ofReal x)) (mem_univ (ENNReal.ofReal y))
    (zero_le (a := a.toNNReal)) (zero_le (a := b.toNNReal)) hab'
  simp only [ENNReal.smul_def, smul_eq_mul] at h_cvx
  simp only [realFun, smul_eq_mul]
  rw [h_eq]
  refine (ENNReal.toReal_mono ?_ h_cvx).trans_eq ?_
  · exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hfx,
      ENNReal.mul_ne_top ENNReal.coe_ne_top hfy⟩
  · rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hfx)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hfy), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.coe_toReal, ENNReal.coe_toReal, Real.coe_toNNReal a ha, Real.coe_toNNReal b hb]

lemma convexOn_Ioo_realFun : ConvexOn ℝ (ENNReal.toReal '' (Ioo f.xmin f.xmax)) f.realFun := by
  refine convexOn_realFun_of_ne_top f ?_ ?_ ?_
  · by_cases h_top : f.xmax = ∞
    · simp only [h_top, ENNReal.toReal_Ioo_top xmin_ne_top]
      exact convex_Ioi _
    · simp only [ENNReal.toReal_Ioo xmin_ne_top h_top]
      exact convex_Ioo _ _
  · rintro _ ⟨x, _, rfl⟩
    exact ENNReal.toReal_nonneg
  · rintro _ ⟨x, hx, rfl⟩
    rw [ENNReal.ofReal_toReal (ne_top_of_lt hx.2)]
    exact (lt_top_of_mem_Ioo hx).ne

lemma convexOn_Ici_realFun (h : ∀ x ≠ ∞, f x ≠ ∞) : ConvexOn ℝ (Ici 0) f.realFun :=
  convexOn_realFun_of_ne_top f (convex_Ici 0) (fun _ hx ↦ hx)
    (fun _ _ ↦ h _ ENNReal.ofReal_ne_top)

lemma differentiableWithinAt {x : ℝ} (hx_nonneg : 0 ≤ x)
    (hx : ENNReal.ofReal x ∈ Ioo f.xmin f.xmax) :
    DifferentiableWithinAt ℝ f.realFun (Ioi x) x := by
  refine f.convexOn_Ioo_realFun.differentiableWithinAt_Ioi_of_mem_interior ?_
  by_cases h_top : f.xmax = ∞
  · simp only [h_top, ENNReal.toReal_Ioo_top xmin_ne_top, interior_Ioi, mem_Ioi]
    exact ENNReal.toReal_lt_of_lt_ofReal hx.1
  · simp only [ne_eq, h_top, not_false_eq_true, ENNReal.toReal_Ioo xmin_ne_top, interior_Ioo,
      mem_Ioo]
    constructor
    · exact ENNReal.toReal_lt_of_lt_ofReal hx.1
    · rw [← ENNReal.ofReal_lt_iff_lt_toReal hx_nonneg h_top]
      exact hx.2

lemma differentiableWithinAt_one : DifferentiableWithinAt ℝ f.realFun (Ioi 1) 1 :=
  f.differentiableWithinAt zero_le_one <| by simp [xmin_lt_one, one_lt_xmax]

lemma isMinOn_realFun_one : IsMinOn f.realFun (ENNReal.toReal '' Ioo f.xmin f.xmax) 1 := by
  intro x _
  simp only [realFun_one, mem_ofPred_eq]
  exact realFun_nonneg _

lemma one_mem_interior_toReal_Ioo_xmin_xmax :
    1 ∈ interior (ENNReal.toReal '' Ioo f.xmin f.xmax) := by
  by_cases h_top : f.xmax = ∞
  · simp only [h_top, ne_eq, xmin_ne_top, not_false_eq_true, ENNReal.toReal_Ioo_top, interior_Ioi,
      mem_Ioi]
    refine ENNReal.toReal_lt_of_lt_ofReal ?_
    simp [xmin_lt_one]
  · simp only [ENNReal.toReal_Ioo xmin_ne_top h_top, interior_Ioo, mem_Ioo]
    constructor
    · refine ENNReal.toReal_lt_of_lt_ofReal ?_
      simp [xmin_lt_one]
    · rw [← ENNReal.ofReal_lt_iff_lt_toReal zero_le_one h_top]
      simp [one_lt_xmax]

lemma leftDeriv_one_nonpos : leftDeriv f.realFun 1 ≤ 0 := by
  refine ConvexOn.leftDeriv_nonpos_of_isMinOn f.convexOn_Ioo_realFun ?_ ?_
  · exact f.isMinOn_realFun_one
  · exact f.one_mem_interior_toReal_Ioo_xmin_xmax

lemma rightDeriv_one_nonneg : 0 ≤ rightDeriv f.realFun 1 := by
  refine ConvexOn.rightDeriv_nonneg_of_isMinOn f.convexOn_Ioo_realFun ?_ ?_
  · exact f.isMinOn_realFun_one
  · exact f.one_mem_interior_toReal_Ioo_xmin_xmax

lemma continuousOn_realFun_Ioo :
    ContinuousOn f.realFun (ENNReal.toReal '' (Ioo f.xmin f.xmax)) := by
  refine ConvexOn.continuousOn ?_ f.convexOn_Ioo_realFun
  by_cases h_top : f.xmax = ∞
  · simp only [h_top, ENNReal.toReal_Ioo_top xmin_ne_top, isOpen_Ioi]
  · simp [h_top, ENNReal.toReal_Ioo xmin_ne_top, isOpen_Ioo]

lemma continuousOn_realFun_Ioi (h : f.xmax = ∞) : ContinuousOn f.realFun (Ioi f.xmin.toReal) := by
  refine ENNReal.continuousOn_toReal.comp
    (f.continuous.comp_continuousOn ENNReal.continuous_ofReal.continuousOn) fun x hx ↦ ?_
  refine (lt_top_of_mem_Ioo ?_).ne
  simp only [h, mem_Ioo, ENNReal.ofReal_lt_top, and_true]
  rw [ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top]
  exact hx

lemma continuousOn_realFun_Ici (h : ∀ x ≠ ∞, f x ≠ ∞) : ContinuousOn f.realFun (Ici 0) :=
  ENNReal.continuousOn_toReal.comp
    (f.continuous.comp_continuousOn ENNReal.continuous_ofReal.continuousOn)
    fun _ _ ↦ h _ ENNReal.ofReal_ne_top

lemma eq_zero_iff {a b : ℝ} (ha : a < 1) (hb : 1 < b)
    (hf_cvx : StrictConvexOn ℝ (Ioo a b) f.realFun) {x : ℝ≥0∞} :
    f x = 0 ↔ x = 1 := by
  have h_iff : (f x = 0 ∧ x ∈ Ioo (ENNReal.ofReal a) (ENNReal.ofReal b)) ↔ x = 1 := by
    refine ⟨fun h ↦ ?_, fun h ↦ ⟨by simp [h], ?_⟩⟩
    · have hx_ne_top : x ≠ ∞ := ne_top_of_lt h.2.2
      suffices x.toReal = 1 by
        rw [← ENNReal.ofReal_toReal hx_ne_top, this, ENNReal.ofReal_one]
      refine StrictConvexOn.eq_of_isMinOn hf_cvx ?_ ?_ ?_ ?_
      · rw [isMinOn_iff]
        intro y hy
        rw [realFun_toReal f hx_ne_top, h.1]
        simp [realFun_nonneg]
      · rw [isMinOn_iff]
        intro y hy
        simp [realFun_nonneg]
      · sorry
      · exact ⟨ha, hb⟩
    · simp [h, ha, hb]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  by_cases hxb : ENNReal.ofReal b ≤ x
  · sorry
  by_cases hxa : x ≤ ENNReal.ofReal a
  · sorry
  exact h_iff.mp ⟨h, ⟨not_le.mp hxa, not_le.mp hxb⟩⟩

end RealFun

variable {f g : DivFunction}

section Module

protected def zero : DivFunction where
  toFun := 0
  one := rfl
  convexOn' := convexOn_const _ convex_univ
  continuous' := continuous_const

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

lemma measurable_divFunction_rnDeriv {f : DivFunction} {μ ν : Measure α} :
    Measurable (fun x ↦ f (μ.rnDeriv ν x)) :=
  f.continuous.measurable.comp (Measure.measurable_rnDeriv _ _)

lemma integral_realFun {g : α → ℝ≥0∞} (hg : Measurable g) (hg_lt : ∀ᵐ x ∂ν, g x < ∞)
    (h_int : ∫⁻ x, f (g x) ∂ν ≠ ∞) :
    ∫ x, f.realFun (g x).toReal ∂ν = (∫⁻ x, f (g x) ∂ν).toReal := by
  have h := ae_lt_top (f.continuous.measurable.comp hg) h_int
  simp_rw [DivFunction.realFun]
  rw [integral_toReal]
  · congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [hg_lt] with x hx
    rw [ENNReal.ofReal_toReal hx.ne]
  · refine (f.continuous.measurable.comp ?_).aemeasurable
    exact hg.ennreal_toReal.ennreal_ofReal
  · filter_upwards [h, hg_lt] with x hx hx'
    rwa [ENNReal.ofReal_toReal hx'.ne]

lemma ofReal_integral_realFun {g : α → ℝ≥0∞} (hg : Measurable g) (hg_lt : ∀ᵐ x ∂ν, g x < ∞)
    (h_int : ∫⁻ x, f (g x) ∂ν ≠ ∞) :
    ENNReal.ofReal (∫ x, f.realFun (g x).toReal ∂ν) = ∫⁻ x, f (g x) ∂ν := by
  rw [integral_realFun hg hg_lt h_int, ENNReal.ofReal_toReal h_int]

lemma integral_realFun_rnDeriv [SigmaFinite μ] (h_int : ∫⁻ x, f (μ.rnDeriv ν x) ∂ν ≠ ∞) :
    ∫ x, f.realFun (μ.rnDeriv ν x).toReal ∂ν = (∫⁻ x, f (μ.rnDeriv ν x) ∂ν).toReal :=
  integral_realFun (μ.measurable_rnDeriv ν) (μ.rnDeriv_lt_top ν) h_int

lemma ofReal_integral_realFun_rnDeriv [SigmaFinite μ] (h_int : ∫⁻ x, f (μ.rnDeriv ν x) ∂ν ≠ ∞) :
    ENNReal.ofReal (∫ x, f.realFun (μ.rnDeriv ν x).toReal ∂ν)
      = ∫⁻ x, f (μ.rnDeriv ν x) ∂ν :=
  ofReal_integral_realFun (μ.measurable_rnDeriv ν) (μ.rnDeriv_lt_top ν) h_int

lemma integrable_realFun_rnDeriv [SigmaFinite μ] (h_int : ∫⁻ x, f (μ.rnDeriv ν x) ∂ν ≠ ∞) :
    Integrable (fun x ↦ f.realFun (μ.rnDeriv ν x).toReal) ν := by
  simp_rw [DivFunction.realFun]
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · refine (f.continuous.measurable.comp ?_).aemeasurable
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.ennreal_ofReal
  · suffices ∫⁻ x, f (ENNReal.ofReal (μ.rnDeriv ν x).toReal) ∂ν = ∫⁻ x, f (μ.rnDeriv ν x) ∂ν by
      rwa [this]
    refine lintegral_congr_ae ?_
    filter_upwards [μ.rnDeriv_lt_top ν] with x hx
    rw [ENNReal.ofReal_toReal hx.ne]

lemma lintegral_eq_top_of_not_integrable_realFun [SigmaFinite μ]
    (h_int : ¬ Integrable (fun x ↦ f.realFun (μ.rnDeriv ν x).toReal) ν) :
    ∫⁻ x, f (μ.rnDeriv ν x) ∂ν = ∞ := by
  by_contra h
  exact h_int (integrable_realFun_rnDeriv h)

section Conj

namespace DivFunction

noncomputable
def conj (f : DivFunction) : DivFunction where
  toFun x := x * f x⁻¹
  one := by simp
  convexOn' := sorry
  continuous' := sorry

end DivFunction

end Conj

end ProbabilityTheory

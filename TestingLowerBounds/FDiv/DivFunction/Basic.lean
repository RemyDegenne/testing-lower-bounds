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

/-- A sequence of rationals in `(a, b)` converging to `a`. -/
lemma exists_rat_seq_tendsto_nhdsGT {a b : ℝ} (hab : a < b) :
    ∃ q : ℕ → ℚ, (∀ n, a < q n ∧ (q n : ℝ) < b) ∧ Tendsto (fun n ↦ (q n : ℝ)) atTop (𝓝 a) := by
  have h : ∀ n : ℕ, a < min b (a + 1 / ((n : ℝ) + 1)) :=
    fun n ↦ lt_min hab (lt_add_of_pos_right a (by positivity))
  choose q hq using fun n ↦ exists_rat_btwn (h n)
  refine ⟨q, fun n ↦ ⟨(hq n).1, (hq n).2.trans_le (min_le_left _ _)⟩, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n ↦ (hq n).1.le)
    (fun n ↦ ((hq n).2.trans_le (min_le_right _ _)).le)
  simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- A sequence of rationals in `(a, b)` converging to `b`. -/
lemma exists_rat_seq_tendsto_nhdsLT {a b : ℝ} (hab : a < b) :
    ∃ q : ℕ → ℚ, (∀ n, a < q n ∧ (q n : ℝ) < b) ∧ Tendsto (fun n ↦ (q n : ℝ)) atTop (𝓝 b) := by
  have h : ∀ n : ℕ, max a (b - 1 / ((n : ℝ) + 1)) < b :=
    fun n ↦ max_lt hab (sub_lt_self b (by positivity))
  choose q hq using fun n ↦ exists_rat_btwn (h n)
  refine ⟨q, fun n ↦ ⟨(le_max_left _ _).trans_lt (hq n).1, (hq n).2⟩, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
    (fun n ↦ ((le_max_right _ _).trans_lt (hq n).1).le) (fun n ↦ (hq n).2.le)
  simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

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

lemma nonneg_of_rightDeriv_one_eq_zero {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hf_one : f 1 = 0) (hf_deriv : rightDeriv f 1 = 0) {x : ℝ} (hx : 0 < x) :
    0 ≤ f x := by
  calc 0
  _ = rightDeriv f 1 * x + (f 1 - rightDeriv f 1 * 1) := by simp [hf_one, hf_deriv]
  _ ≤ f x := hf.affine_le_of_mem_interior
    ((interior_Ioi (a := (0 : ℝ))).symm ▸ mem_Ioi.mpr zero_lt_one) hx

lemma nonneg_of_leftDeriv_one_nonpos_of_rightDeriv_one_nonneg {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f)
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

@[ext] lemma ext {f g : DivFunction} (h : ∀ x, f x = g x) : f = g := by
  exact (DivFunction.mk.injEq ..).mpr (funext h)

section Def
variable (f : DivFunction)

@[simp] lemma apply_one : f 1 = 0 := f.one

lemma convexOn : ConvexOn ℝ≥0 univ f := f.convexOn'

lemma continuous : Continuous f := f.continuous'

lemma measurable : Measurable f := f.continuous.measurable

/-- The real function `x ↦ (f (ENNReal.ofReal x)).toReal` associated with a `DivFunction`. -/
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

lemma apply_eq_zero_of_le_one (h0 : f 0 = 0) {x : ℝ≥0∞} (hx : x ≤ 1) : f x = 0 :=
  le_antisymm ((f.antitoneOn (mem_Iic.2 zero_le_one) (mem_Iic.2 hx) zero_le).trans_eq h0)
    zero_le

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

/-- The set of nonnegative reals at which `f` is finite is convex. -/
lemma convex_setOf_ne_top : Convex ℝ {x : ℝ | 0 ≤ x ∧ f (ENNReal.ofReal x) ≠ ∞} := by
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ?_⟩
  have h_eq : ENNReal.ofReal (a * x + b * y)
      = ↑a.toNNReal * ENNReal.ofReal x + ↑b.toNNReal * ENNReal.ofReal y := by
    rw [ENNReal.ofReal_add (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ENNReal.ofReal_mul ha,
      ENNReal.ofReal_mul hb]
    rfl
  have hab' : a.toNNReal + b.toNNReal = 1 := by
    rw [← Real.toNNReal_add ha hb, hab, Real.toNNReal_one]
  have h_cvx := f.convexOn.2 (mem_univ (ENNReal.ofReal x)) (mem_univ (ENNReal.ofReal y))
    (zero_le (a := a.toNNReal)) (zero_le (a := b.toNNReal)) hab'
  simp only [ENNReal.smul_def, smul_eq_mul] at h_cvx
  rw [h_eq]
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hx.2,
    ENNReal.mul_ne_top ENNReal.coe_ne_top hy.2⟩) h_cvx

lemma convexOn_realFun_setOf_ne_top :
    ConvexOn ℝ {x : ℝ | 0 ≤ x ∧ f (ENNReal.ofReal x) ≠ ∞} f.realFun :=
  f.convexOn_realFun_of_ne_top f.convex_setOf_ne_top (fun _ hx ↦ hx.1) (fun _ hx ↦ hx.2)

lemma toReal_mem_interior_setOf_ne_top {x : ℝ≥0∞} (hx : x ∈ Ioo f.xmin f.xmax) :
    x.toReal ∈ interior {y : ℝ | 0 ≤ y ∧ f (ENNReal.ofReal y) ≠ ∞} := by
  have h_sub : ENNReal.toReal '' Ioo f.xmin f.xmax
      ⊆ {y : ℝ | 0 ≤ y ∧ f (ENNReal.ofReal y) ≠ ∞} := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    rw [ENNReal.ofReal_toReal (ne_top_of_lt hz.2)]
    exact (f.lt_top_of_mem_Ioo hz).ne
  have h_open : IsOpen (ENNReal.toReal '' Ioo f.xmin f.xmax) := by
    by_cases h_top : f.xmax = ∞
    · rw [h_top, ENNReal.toReal_Ioo_top xmin_ne_top]
      exact isOpen_Ioi
    · rw [ENNReal.toReal_Ioo xmin_ne_top h_top]
      exact isOpen_Ioo
  refine interior_mono h_sub ?_
  rw [h_open.interior_eq]
  exact mem_image_of_mem _ hx

/-- Supporting line of the convex function `f.realFun` at an interior point of its finiteness
set. -/
lemma realFun_add_rightDeriv_mul_sub_le {x y : ℝ}
    (hx : x ∈ interior {y : ℝ | 0 ≤ y ∧ f (ENNReal.ofReal y) ≠ ∞})
    (hy : y ∈ {y : ℝ | 0 ≤ y ∧ f (ENNReal.ofReal y) ≠ ∞}) :
    f.realFun x + rightDeriv f.realFun x * (y - x) ≤ f.realFun y := by
  have hfc := f.convexOn_realFun_setOf_ne_top
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := hfc.rightDeriv_le_slope_of_mem_interior hx hy hxy
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at h
    simp only [rightDeriv]
    linarith
  · simp
  · have h := hfc.slope_le_leftDeriv_of_mem_interior hy hx hyx
    have h' := hfc.leftDeriv_le_rightDeriv_of_mem_interior hx
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hyx)] at h
    have := mul_le_mul_of_nonneg_right h' (sub_pos.mpr hyx).le
    simp only [rightDeriv]
    linarith

/-- Supporting line inequality for `f`, written without subtraction in `ℝ≥0∞`. -/
lemma apply_add_le_apply_add {x : ℝ≥0∞} (hx : x ∈ Ioo f.xmin f.xmax) {y : ℝ≥0∞} (hy : y ≠ ∞) :
    f x + ENNReal.ofReal (max (rightDeriv f.realFun x.toReal) 0) * y
        + ENNReal.ofReal (max (-rightDeriv f.realFun x.toReal) 0) * x
      ≤ f y + ENNReal.ofReal (max (rightDeriv f.realFun x.toReal) 0) * x
        + ENNReal.ofReal (max (-rightDeriv f.realFun x.toReal) 0) * y := by
  by_cases hfy : f y = ∞
  · rw [hfy, top_add, top_add]
    exact le_top
  have hx_top : x ≠ ∞ := ne_top_of_lt hx.2
  have hfx : f x ≠ ∞ := (f.lt_top_of_mem_Ioo hx).ne
  have h_tangent := f.realFun_add_rightDeriv_mul_sub_le (f.toReal_mem_interior_setOf_ne_top hx)
    (y := y.toReal) ⟨ENNReal.toReal_nonneg, by rwa [ENNReal.ofReal_toReal hy]⟩
  rw [realFun_toReal f hx_top, realFun_toReal f hy] at h_tangent
  set c := rightDeriv f.realFun x.toReal with hc
  have key : c * (y.toReal - x.toReal)
      = max c 0 * y.toReal + max (-c) 0 * x.toReal
        - (max c 0 * x.toReal + max (-c) 0 * y.toReal) := by
    calc c * (y.toReal - x.toReal) = (max c 0 - max (-c) 0) * (y.toReal - x.toReal) := by
          rw [max_zero_sub_max_neg_zero_eq_self]
      _ = _ := by ring
  have e1 : ENNReal.ofReal ((f x).toReal + max c 0 * y.toReal + max (-c) 0 * x.toReal)
      = f x + ENNReal.ofReal (max c 0) * y + ENNReal.ofReal (max (-c) 0) * x := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_mul (le_max_right _ _),
      ENNReal.ofReal_toReal hfx, ENNReal.ofReal_toReal hy, ENNReal.ofReal_toReal hx_top]
  have e2 : ENNReal.ofReal ((f y).toReal + max c 0 * x.toReal + max (-c) 0 * y.toReal)
      = f y + ENNReal.ofReal (max c 0) * x + ENNReal.ofReal (max (-c) 0) * y := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_mul (le_max_right _ _),
      ENNReal.ofReal_toReal hfy, ENNReal.ofReal_toReal hy, ENNReal.ofReal_toReal hx_top]
  rw [← e1, ← e2]
  exact ENNReal.ofReal_le_ofReal (by linarith)

lemma monotoneOn_rightDeriv_realFun :
    MonotoneOn (rightDeriv f.realFun) (interior {x : ℝ | 0 ≤ x ∧ f (ENNReal.ofReal x) ≠ ∞}) :=
  f.convexOn_realFun_setOf_ne_top.monotoneOn_rightDeriv

lemma rightDeriv_realFun_toReal_mono {x y : ℝ≥0∞} (hx : x ∈ Ioo f.xmin f.xmax)
    (hy : y ∈ Ioo f.xmin f.xmax) (hxy : x ≤ y) :
    rightDeriv f.realFun x.toReal ≤ rightDeriv f.realFun y.toReal :=
  f.monotoneOn_rightDeriv_realFun (f.toReal_mem_interior_setOf_ne_top hx)
    (f.toReal_mem_interior_setOf_ne_top hy) (ENNReal.toReal_mono (ne_top_of_lt hy.2) hxy)

/-- Consequence of the supporting line inequality at `x ≤ y`. -/
lemma apply_le_add_of_le {x y g : ℝ≥0∞} (hx_top : x ≠ ∞) (hxy : x ≤ y) {c : ℝ}
    (h : f x + ENNReal.ofReal (max c 0) * y + ENNReal.ofReal (max (-c) 0) * x
      ≤ g + ENNReal.ofReal (max c 0) * x + ENNReal.ofReal (max (-c) 0) * y) :
    f x ≤ g + ENNReal.ofReal (max (-c) 0) * (y - x) := by
  have hy' : y = x + (y - x) := (add_tsub_cancel_of_le hxy).symm
  rw [hy', mul_add, mul_add] at h
  have hfin : ENNReal.ofReal (max c 0) * x + ENNReal.ofReal (max (-c) 0) * x ≠ ∞ := by
    simp [ENNReal.mul_ne_top, hx_top]
  calc f x ≤ f x + ENNReal.ofReal (max c 0) * (y - x) := le_self_add
    _ ≤ g + ENNReal.ofReal (max (-c) 0) * (y - x) := by
        refine ENNReal.le_of_add_le_add_right hfin ?_
        calc f x + ENNReal.ofReal (max c 0) * (y - x)
              + (ENNReal.ofReal (max c 0) * x + ENNReal.ofReal (max (-c) 0) * x)
            = f x + (ENNReal.ofReal (max c 0) * x + ENNReal.ofReal (max c 0) * (y - x))
              + ENNReal.ofReal (max (-c) 0) * x := by ring
          _ ≤ g + ENNReal.ofReal (max c 0) * x
              + (ENNReal.ofReal (max (-c) 0) * x + ENNReal.ofReal (max (-c) 0) * (y - x)) := h
          _ = g + ENNReal.ofReal (max (-c) 0) * (y - x)
              + (ENNReal.ofReal (max c 0) * x + ENNReal.ofReal (max (-c) 0) * x) := by ring

/-- Consequence of the supporting line inequality at `x ≥ y`. -/
lemma apply_le_add_of_ge {x y g : ℝ≥0∞} (hy_top : y ≠ ∞) (hyx : y ≤ x) {c : ℝ}
    (h : f x + ENNReal.ofReal (max c 0) * y + ENNReal.ofReal (max (-c) 0) * x
      ≤ g + ENNReal.ofReal (max c 0) * x + ENNReal.ofReal (max (-c) 0) * y) :
    f x ≤ g + ENNReal.ofReal (max c 0) * (x - y) := by
  have e1 : ENNReal.ofReal (max c 0) * x
      = ENNReal.ofReal (max c 0) * y + ENNReal.ofReal (max c 0) * (x - y) := by
    rw [← mul_add, add_tsub_cancel_of_le hyx]
  have e2 : ENNReal.ofReal (max (-c) 0) * x
      = ENNReal.ofReal (max (-c) 0) * y + ENNReal.ofReal (max (-c) 0) * (x - y) := by
    rw [← mul_add, add_tsub_cancel_of_le hyx]
  rw [e1, e2] at h
  have hfin : ENNReal.ofReal (max c 0) * y + ENNReal.ofReal (max (-c) 0) * y ≠ ∞ := by
    simp [ENNReal.mul_ne_top, hy_top]
  calc f x ≤ f x + ENNReal.ofReal (max (-c) 0) * (x - y) := le_self_add
    _ ≤ g + ENNReal.ofReal (max c 0) * (x - y) := by
        refine ENNReal.le_of_add_le_add_right hfin ?_
        calc f x + ENNReal.ofReal (max (-c) 0) * (x - y)
              + (ENNReal.ofReal (max c 0) * y + ENNReal.ofReal (max (-c) 0) * y)
            = f x + ENNReal.ofReal (max c 0) * y
              + (ENNReal.ofReal (max (-c) 0) * y + ENNReal.ofReal (max (-c) 0) * (x - y)) := by ring
          _ ≤ g + (ENNReal.ofReal (max c 0) * y + ENNReal.ofReal (max c 0) * (x - y))
              + ENNReal.ofReal (max (-c) 0) * y := h
          _ = g + ENNReal.ofReal (max c 0) * (x - y)
              + (ENNReal.ofReal (max c 0) * y + ENNReal.ofReal (max (-c) 0) * y) := by ring

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
  set c : ℝ≥0∞ → ℝ := fun x ↦ rightDeriv f.realFun x.toReal with hc
  have h_below : ∀ q : ℚ, ENNReal.ofReal q ∈ Ioo f.xmin f.xmax → ENNReal.ofReal q ≤ y →
      f (ENNReal.ofReal q)
        ≤ g + ENNReal.ofReal (max (-c (ENNReal.ofReal q)) 0) * (y - ENNReal.ofReal q) :=
    fun q hq hqy ↦ f.apply_le_add_of_le ENNReal.ofReal_ne_top hqy (h q hq)
  have h_above : ∀ q : ℚ, ENNReal.ofReal q ∈ Ioo f.xmin f.xmax → y ≤ ENNReal.ofReal q →
      f (ENNReal.ofReal q)
        ≤ g + ENNReal.ofReal (max (c (ENNReal.ofReal q)) 0) * (ENNReal.ofReal q - y) :=
    fun q hq hqy ↦ f.apply_le_add_of_ge hy_top hqy (h q hq)
  have h_tendsto_ofReal {q : ℕ → ℚ} {a : ℝ} (hq : Tendsto (fun n ↦ (q n : ℝ)) atTop (𝓝 a)) :
      Tendsto (fun n ↦ ENNReal.ofReal (q n)) atTop (𝓝 (ENNReal.ofReal a)) :=
    (ENNReal.continuous_ofReal.tendsto a).comp hq
  rcases lt_or_ge y f.xmax with hy_lt | hy_ge
  · rcases lt_or_ge f.xmin y with hy_gt | hy_le
    · -- interior point: approach `y` from below
      have hy_toReal : f.xmin.toReal < y.toReal := ENNReal.toReal_strict_mono hy_top hy_gt
      set a : ℝ := (f.xmin.toReal + y.toReal) / 2 with ha
      have ha_gt : f.xmin.toReal < a := by rw [ha]; linarith
      have ha_lt : a < y.toReal := by rw [ha]; linarith
      have ha_pos : 0 < a := lt_of_le_of_lt ENNReal.toReal_nonneg ha_gt
      have ha_mem : ENNReal.ofReal a ∈ Ioo f.xmin f.xmax := by
        refine ⟨?_, (ENNReal.ofReal_lt_iff_lt_toReal ha_pos.le hy_top).mpr ha_lt |>.trans hy_lt⟩
        rw [← ENNReal.ofReal_toReal xmin_ne_top]
        exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨ha_gt, ha_pos⟩
      obtain ⟨q, hq, hq_tendsto⟩ := exists_rat_seq_tendsto_nhdsLT ha_lt
      have hq_mem : ∀ n, ENNReal.ofReal (q n) ∈ Ioo f.xmin f.xmax := fun n ↦
        ⟨ha_mem.1.trans_le (ENNReal.ofReal_le_ofReal (hq n).1.le),
          ((ENNReal.ofReal_lt_iff_lt_toReal (ha_pos.trans (hq n).1).le hy_top).mpr (hq n).2).trans
            hy_lt⟩
      have hq_le : ∀ n, ENNReal.ofReal (q n) ≤ y := fun n ↦
        ((ENNReal.ofReal_lt_iff_lt_toReal (ha_pos.trans (hq n).1).le hy_top).mpr (hq n).2).le
      have h_bound : ∀ n, f (ENNReal.ofReal (q n))
          ≤ g + ENNReal.ofReal (max (-c (ENNReal.ofReal a)) 0) * (y - ENNReal.ofReal (q n)) := by
        intro n
        refine (h_below (q n) (hq_mem n) (hq_le n)).trans ?_
        gcongr
        exact f.rightDeriv_realFun_toReal_mono ha_mem (hq_mem n)
          (ENNReal.ofReal_le_ofReal (hq n).1.le)
      have h_lim_q : Tendsto (fun n ↦ ENNReal.ofReal (q n)) atTop (𝓝 y) := by
        simpa [ENNReal.ofReal_toReal hy_top] using h_tendsto_ofReal hq_tendsto
      refine le_of_tendsto_of_tendsto' ((f.continuous.tendsto y).comp h_lim_q) ?_ h_bound
      have : Tendsto (fun n ↦ g + ENNReal.ofReal (max (-c (ENNReal.ofReal a)) 0)
          * (y - ENNReal.ofReal (q n))) atTop
          (𝓝 (g + ENNReal.ofReal (max (-c (ENNReal.ofReal a)) 0) * (y - y))) :=
        tendsto_const_nhds.add (ENNReal.Tendsto.const_mul
          (ENNReal.Tendsto.sub tendsto_const_nhds h_lim_q (Or.inl hy_top))
          (Or.inr ENNReal.ofReal_ne_top))
      simpa using this
    · -- `y ≤ xmin`
      rcases eq_or_ne f.xmin 0 with h0 | h0
      · -- then `y = 0`: approach `0` from above
        have hy0 : y = 0 := le_antisymm (h0 ▸ hy_le) bot_le
        obtain ⟨q, hq, hq_tendsto⟩ := exists_rat_seq_tendsto_nhdsGT (zero_lt_one' ℝ)
        have hq_mem : ∀ n, ENNReal.ofReal (q n) ∈ Ioo f.xmin f.xmax := fun n ↦
          ⟨h0 ▸ ENNReal.ofReal_pos.mpr (hq n).1,
            (ENNReal.ofReal_lt_one.mpr (hq n).2).trans one_lt_xmax⟩
        have h_bound : ∀ n, f (ENNReal.ofReal (q n))
            ≤ g + ENNReal.ofReal (max (c 1) 0) * (ENNReal.ofReal (q n) - y) := by
          intro n
          refine (h_above (q n) (hq_mem n) (by rw [hy0]; exact bot_le)).trans ?_
          gcongr
          exact f.rightDeriv_realFun_toReal_mono (hq_mem n) h1
            (ENNReal.ofReal_le_one.mpr (hq n).2.le)
        have h_lim_q : Tendsto (fun n ↦ ENNReal.ofReal (q n)) atTop (𝓝 y) := by
          simpa [hy0] using h_tendsto_ofReal hq_tendsto
        refine le_of_tendsto_of_tendsto' ((f.continuous.tendsto y).comp h_lim_q) ?_ h_bound
        have : Tendsto (fun n ↦ g + ENNReal.ofReal (max (c 1) 0) * (ENNReal.ofReal (q n) - y))
            atTop (𝓝 (g + ENNReal.ofReal (max (c 1) 0) * (y - y))) :=
          tendsto_const_nhds.add (ENNReal.Tendsto.const_mul
            (ENNReal.Tendsto.sub h_lim_q tendsto_const_nhds (Or.inr hy_top))
            (Or.inr ENNReal.ofReal_ne_top))
        simpa using this
      · -- `0 < xmin`, so `f xmin = ∞`: approach `xmin` from above, which forces `g = ∞`
        have hmin_pos : 0 < f.xmin := pos_iff_ne_zero.mpr h0
        have hmin_lt : f.xmin.toReal < 1 := by
          rw [← ENNReal.toReal_one]
          exact ENNReal.toReal_strict_mono ENNReal.one_ne_top xmin_lt_one
        obtain ⟨q, hq, hq_tendsto⟩ := exists_rat_seq_tendsto_nhdsGT hmin_lt
        have hq_mem : ∀ n, ENNReal.ofReal (q n) ∈ Ioo f.xmin f.xmax := fun n ↦
          ⟨by
            rw [← ENNReal.ofReal_toReal xmin_ne_top]
            exact ENNReal.ofReal_lt_ofReal_iff'.mpr
              ⟨(hq n).1, ENNReal.toReal_nonneg.trans_lt (hq n).1⟩,
            (ENNReal.ofReal_lt_one.mpr (hq n).2).trans one_lt_xmax⟩
        have h_bound : ∀ n, f (ENNReal.ofReal (q n))
            ≤ g + ENNReal.ofReal (max (c 1) 0) * (ENNReal.ofReal (q n) - y) := by
          intro n
          refine (h_above (q n) (hq_mem n) (hy_le.trans (hq_mem n).1.le)).trans ?_
          gcongr
          exact f.rightDeriv_realFun_toReal_mono (hq_mem n) h1
            (ENNReal.ofReal_le_one.mpr (hq n).2.le)
        have h_lim_q : Tendsto (fun n ↦ ENNReal.ofReal (q n)) atTop (𝓝 f.xmin) := by
          simpa [ENNReal.ofReal_toReal xmin_ne_top] using h_tendsto_ofReal hq_tendsto
        have h_lim_f : Tendsto (fun n ↦ f (ENNReal.ofReal (q n))) atTop (𝓝 ∞) := by
          rw [← f.apply_xmin_eq_top hmin_pos]
          exact (f.continuous.tendsto _).comp h_lim_q
        have h_lim_g : Tendsto (fun n ↦ g + ENNReal.ofReal (max (c 1) 0)
            * (ENNReal.ofReal (q n) - y)) atTop
            (𝓝 (g + ENNReal.ofReal (max (c 1) 0) * (f.xmin - y))) :=
          tendsto_const_nhds.add (ENNReal.Tendsto.const_mul
            (ENNReal.Tendsto.sub h_lim_q tendsto_const_nhds (Or.inr hy_top))
            (Or.inr ENNReal.ofReal_ne_top))
        have h_top := le_of_tendsto_of_tendsto' h_lim_f h_lim_g h_bound
        rw [top_le_iff, ENNReal.add_eq_top] at h_top
        rcases h_top with hg | hg
        · rw [hg]; exact le_top
        · exact absurd hg (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.sub_ne_top xmin_ne_top))
  · -- `xmax ≤ y`, so `xmax < ∞` and `f xmax = ∞`: approach `xmax` from below, forcing `g = ∞`
    have hmax_top : f.xmax ≠ ∞ := ne_top_of_le_ne_top hy_top hy_ge
    have hmax_gt : 1 < f.xmax.toReal := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_strict_mono hmax_top one_lt_xmax
    obtain ⟨q, hq, hq_tendsto⟩ := exists_rat_seq_tendsto_nhdsLT hmax_gt
    have hq_mem : ∀ n, ENNReal.ofReal (q n) ∈ Ioo f.xmin f.xmax := fun n ↦
      ⟨xmin_lt_one.trans (ENNReal.one_lt_ofReal.mpr (hq n).1),
        (ENNReal.ofReal_lt_iff_lt_toReal (zero_le_one.trans (hq n).1.le) hmax_top).mpr (hq n).2⟩
    have h_bound : ∀ n, f (ENNReal.ofReal (q n))
        ≤ g + ENNReal.ofReal (max (-c 1) 0) * (y - ENNReal.ofReal (q n)) := by
      intro n
      refine (h_below (q n) (hq_mem n) ((hq_mem n).2.le.trans hy_ge)).trans ?_
      gcongr
      exact f.rightDeriv_realFun_toReal_mono h1 (hq_mem n) (ENNReal.one_le_ofReal.mpr (hq n).1.le)
    have h_lim_q : Tendsto (fun n ↦ ENNReal.ofReal (q n)) atTop (𝓝 f.xmax) := by
      simpa [ENNReal.ofReal_toReal hmax_top] using h_tendsto_ofReal hq_tendsto
    have h_lim_f : Tendsto (fun n ↦ f (ENNReal.ofReal (q n))) atTop (𝓝 ∞) := by
      rw [← f.apply_xmax_eq_top hmax_top]
      exact (f.continuous.tendsto _).comp h_lim_q
    have h_lim_g : Tendsto (fun n ↦ g + ENNReal.ofReal (max (-c 1) 0)
        * (y - ENNReal.ofReal (q n))) atTop
        (𝓝 (g + ENNReal.ofReal (max (-c 1) 0) * (y - f.xmax))) :=
      tendsto_const_nhds.add (ENNReal.Tendsto.const_mul
        (ENNReal.Tendsto.sub tendsto_const_nhds h_lim_q (Or.inl hy_top))
        (Or.inr ENNReal.ofReal_ne_top))
    have h_top := le_of_tendsto_of_tendsto' h_lim_f h_lim_g h_bound
    rw [top_le_iff, ENNReal.add_eq_top] at h_top
    rcases h_top with hg | hg
    · rw [hg]; exact le_top
    · exact absurd hg (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sub_ne_top hy_top))

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
  have h_iff : ∀ z : ℝ≥0∞, (f z = 0 ∧ z ∈ Ioo (ENNReal.ofReal a) (ENNReal.ofReal b)) ↔ z = 1 := by
    intro z
    refine ⟨fun h ↦ ?_, fun h ↦ ⟨by simp [h], ?_⟩⟩
    · have hz_ne_top : z ≠ ∞ := ne_top_of_lt h.2.2
      suffices z.toReal = 1 by
        rw [← ENNReal.ofReal_toReal hz_ne_top, this, ENNReal.ofReal_one]
      refine StrictConvexOn.eq_of_isMinOn hf_cvx ?_ ?_ ?_ ?_
      · rw [isMinOn_iff]
        intro y hy
        rw [realFun_toReal f hz_ne_top, h.1]
        simp [realFun_nonneg]
      · rw [isMinOn_iff]
        intro y hy
        simp [realFun_nonneg]
      · refine ⟨?_, (ENNReal.lt_ofReal_iff_toReal_lt hz_ne_top).mp h.2.2⟩
        rcases le_or_gt a 0 with ha0 | ha0
        · have hz0 : 0 < z := by
            have := h.2.1
            rwa [ENNReal.ofReal_of_nonpos ha0] at this
          exact ha0.trans_lt (ENNReal.toReal_pos hz0.ne' hz_ne_top)
        · exact (ENNReal.ofReal_lt_iff_lt_toReal ha0.le hz_ne_top).mp h.2.1
      · exact ⟨ha, hb⟩
    · simp [h, ha, hb]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  by_cases hxb : ENNReal.ofReal b ≤ x
  · exfalso
    set y : ℝ := (1 + b) / 2 with hy_def
    have hy1 : 1 < y := by rw [hy_def]; linarith
    have hyb : y < b := by rw [hy_def]; linarith
    have hy_mem : ENNReal.ofReal y ∈ Ioo (ENNReal.ofReal a) (ENNReal.ofReal b) :=
      ⟨ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨ha.trans hy1, by linarith⟩,
        ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hyb, by linarith⟩⟩
    have hyx : ENNReal.ofReal y ≤ x := hy_mem.2.le.trans hxb
    have h_le : f (ENNReal.ofReal y) ≤ f x :=
      f.monotoneOn (ENNReal.one_le_ofReal.mpr hy1.le)
        ((ENNReal.one_le_ofReal.mpr hy1.le).trans hyx) hyx
    rw [h] at h_le
    have h0 := (h_iff _).mp ⟨le_antisymm h_le (by simp), hy_mem⟩
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff (by linarith) zero_le_one] at h0
    linarith
  by_cases hxa : x ≤ ENNReal.ofReal a
  · exfalso
    set y : ℝ := (max a 0 + 1) / 2 with hy_def
    have hmax : max a 0 < 1 := max_lt ha zero_lt_one
    have hy0 : 0 < y := by rw [hy_def]; positivity
    have hy1 : y < 1 := by rw [hy_def]; linarith
    have hay : a < y := by rw [hy_def]; have := le_max_left a 0; linarith
    have hy_mem : ENNReal.ofReal y ∈ Ioo (ENNReal.ofReal a) (ENNReal.ofReal b) :=
      ⟨ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hay, hy0⟩,
        ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hy1.trans hb, by linarith⟩⟩
    have hxy : x ≤ ENNReal.ofReal y := hxa.trans (ENNReal.ofReal_le_ofReal hay.le)
    have h_le : f (ENNReal.ofReal y) ≤ f x :=
      f.antitoneOn (hxy.trans (ENNReal.ofReal_le_one.mpr hy1.le))
        (ENNReal.ofReal_le_one.mpr hy1.le) hxy
    rw [h] at h_le
    have h0 := (h_iff _).mp ⟨le_antisymm h_le (by simp), hy_mem⟩
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff hy0.le zero_le_one] at h0
    linarith
  exact (h_iff x).mp ⟨h, ⟨not_le.mp hxa, not_le.mp hxb⟩⟩

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

end ProbabilityTheory

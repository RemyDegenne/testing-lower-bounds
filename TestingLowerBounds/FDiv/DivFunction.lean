/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import TestingLowerBounds.Convex
import TestingLowerBounds.DerivAtTop
import TestingLowerBounds.FDiv.ERealStieltjes
import TestingLowerBounds.ForMathlib.Integrable
import TestingLowerBounds.ForMathlib.RnDeriv

/-!

# f-Divergences functions

-/

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

instance : OrderedSMul ℝ≥0 ℝ≥0∞ := by
  constructor
  intro a b u hab hu
  simp_rw [ENNReal.smul_def, smul_eq_mul]
  · rw [ENNReal.mul_lt_mul_left]
    · exact hab
    · simp [hu.ne']
    · exact ENNReal.coe_ne_top
  · intro a b u h_lt h_pos
    simp_rw [ENNReal.smul_def, smul_eq_mul] at h_lt
    rw [ENNReal.mul_lt_mul_left] at h_lt
    · exact h_lt
    · simp [h_pos.ne']
    · exact ENNReal.coe_ne_top

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
    exact ⟨x, fun z hz ↦ if_pos hz⟩
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

lemma leftDeriv_congr {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝[<] x] g) (hx : f x = g x) :
    leftDeriv f x = leftDeriv g x := h.derivWithin_eq hx

lemma rightDeriv_congr {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝[>] x] g) (hx : f x = g x) :
    rightDeriv f x = rightDeriv g x := h.derivWithin_eq hx

namespace ConvexOn

lemma nonneg_of_todo {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hf_one : f 1 = 0) (hf_deriv : rightDeriv f 1 = 0) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ f x := by
  calc 0
  _ = rightDeriv f 1 * x + (f 1 - rightDeriv f 1 * 1) := by simp [hf_one, hf_deriv]
  _ ≤ f x := hf.affine_le_of_mem_interior sorry sorry

lemma nonneg_of_todo' {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hf_one : f 1 = 0) (hf_ld : leftDeriv f 1 ≤ 0) (hf_rd : 0 ≤ rightDeriv f 1)
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ f x := by
  sorry

lemma leftDeriv_nonpos_of_isMinOn {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) {x₀ : ℝ}
    (hf_one : IsMinOn f s x₀) (h_mem : x₀ ∈ interior s) :
    leftDeriv f x₀ ≤ 0 := by
  sorry

lemma rightDeriv_nonneg_of_isMinOn {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) {x₀ : ℝ}
    (hf_one : IsMinOn f s x₀) (h_mem : x₀ ∈ interior s) :
    0 ≤ rightDeriv f x₀ := by
  sorry

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

section EffectiveDomain
variable {f : DivFunction}

lemma eventually_ne_top_nhds_one (f : DivFunction) : ∀ᶠ a in 𝓝 1, f a ≠ ∞ := by
  suffices ∀ᶠ a in 𝓝 1, f a < 1 by
    filter_upwards [this] with x hx using ne_top_of_lt hx
  refine eventually_lt_of_tendsto_lt ?_ (f.continuous.tendsto 1)
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
  refine eventually_lt_of_tendsto_lt ?_ (f.continuous.tendsto 1)
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
  exact not_le_of_lt hx_lt (sInf_le h_eq)

lemma eq_top_of_xmax_lt {x : ℝ≥0∞} (hx_gt : f.xmax < x) : f x = ∞ := by
  rw [xmax] at hx_gt
  by_contra h_eq
  exact not_le_of_lt hx_gt (le_sSup h_eq)

lemma lt_top_of_mem_Ioo {x : ℝ≥0∞} (hx : x ∈ Ioo f.xmin f.xmax) : f x < ∞ := by
  rw [mem_Ioo, xmin, sInf_lt_iff, xmax, lt_sSup_iff] at hx
  obtain ⟨a, ha, hax⟩ := hx.1
  obtain ⟨b, hb, hxb⟩ := hx.2
  calc f x
  _ ≤ max (f a) (f b) := by
    -- todo: should be ConvexOn.le_max_of_mem_Icc but that does not work with ℝ≥0∞
    have h := f.convexOn.2 (mem_univ a) (mem_univ b)
    obtain ⟨u, v, huv, rfl⟩ : ∃ (u : ℝ≥0) (v : ℝ≥0), u + v = 1 ∧ u • a + v • b = x := by
      have h_mem : x ∈ Icc a b := ⟨hax.le, hxb.le⟩
      have h_cvx : Convex ℝ≥0 (Icc a b) := convex_Icc _ _
      -- refine Convex.exists_mem_add_smul_eq
      sorry
    refine (h (zero_le u) (zero_le v) huv).trans ?_
    sorry
  _ < ∞ := sorry

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

lemma convexOn_Ioo_realFun : ConvexOn ℝ (ENNReal.toReal '' (Ioo f.xmin f.xmax)) f.realFun := by
  sorry

lemma convexOn_Ici_realFun (h : ∀ x ≠ ∞, f x ≠ ∞) : ConvexOn ℝ (Ici 0) f.realFun := sorry

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

@[simp] lemma leftDeriv_one_nonpos : leftDeriv f.realFun 1 ≤ 0 := by
  sorry

@[simp] lemma rightDeriv_one_nonneg : 0 ≤ rightDeriv f.realFun 1 := by
  sorry

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

lemma continuousOn_realFun_Ici (h : ∀ x ≠ ∞, f x ≠ ∞) : ContinuousOn f.realFun (Ici 0) := by
  -- refine ENNReal.continuousOn_toReal.comp ?_
  --  (f.continuous.comp_continuousOn ENNReal.continuous_ofReal.continuousOn) fun _ _ ↦ h _
  sorry

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
      · sorry
    · simp [h, ha, hb]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  by_cases hxb : ENNReal.ofReal b ≤ x
  · sorry
  by_cases hxa : x ≤ ENNReal.ofReal a
  · sorry
  exact h_iff.mp ⟨h, ⟨not_le.mp hxa, not_le.mp hxb⟩⟩

end RealFun

lemma monotoneOn (f : DivFunction) : MonotoneOn f (Ici 1) := sorry

lemma antitoneOn (f : DivFunction) : AntitoneOn f (Iic 1) := sorry

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
    convexOn' := f.convexOn.smul c.2
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

@[simp] lemma xmin_zero : (0 : DivFunction).xmin = 0 := by
  sorry

@[simp] lemma xmax_zero : (0 : DivFunction).xmax = ∞ := by
  sorry

@[simp] lemma xmin_add : (f + g).xmin = max f.xmin g.xmin := by
  sorry

@[simp] lemma xmax_add : (f + g).xmax = min f.xmax g.xmax := by
  sorry

@[simp] lemma xmin_smul {c : ℝ≥0} : (c • f).xmin = c * f.xmin := by
  sorry

@[simp] lemma xmax_smul {c : ℝ≥0} (hc : c ≠ 0) : (c • f).xmax = c * f.xmax := by
  sorry

section RightDeriv

lemma rightDeriv_mono (f : DivFunction) {x y : ℝ} (hxy : x ≤ y)
    (hx : f.xmin < ENNReal.ofReal x) (hy : ENNReal.ofReal y < f.xmax) :
    rightDeriv f.realFun x ≤ rightDeriv f.realFun y := by
  sorry

lemma continuousWithinAt_rightDeriv (f : DivFunction) {x : ℝ}
    (hx : f.xmin < ENNReal.ofReal x) (hx' : ENNReal.ofReal x < f.xmax) :
    ContinuousWithinAt (rightDeriv f.realFun) (Ici x) x := by
  sorry

-- the `rightLim` matters only at `f.xmin`: `rightDeriv` could be 0 because it has no limit in `ℝ`,
-- but in that case it should be `⊥`.
protected noncomputable def rightDerivStieltjes (f : DivFunction) : ERealStieltjes where
  toFun := fun x ↦
    if x < f.xmin.toReal then ⊥
    else if f.xmax ≤ ENNReal.ofReal x then ⊤
    else Function.rightLim (fun y ↦ (rightDeriv f.realFun y : EReal)) x
  mono' x y hxy := sorry
  right_continuous' x := sorry

lemma rightDerivStieltjes_of_lt_xmin {x : ℝ} (hx : x < f.xmin.toReal) :
    f.rightDerivStieltjes x = ⊥ := if_pos hx

lemma rightDerivStieltjes_of_ge_xmax {x : ℝ} (hx : f.xmax ≤ ENNReal.ofReal x) :
    f.rightDerivStieltjes x = ⊤ := by
  simp only [DivFunction.rightDerivStieltjes]
  rw [if_neg, if_pos hx]
  rw [not_lt]
  refine ENNReal.toReal_le_of_le_ofReal ?_ (xmin_lt_xmax.le.trans hx)
  have hx' : 0 < ENNReal.ofReal x := xmax_pos.trans_le hx
  simp only [ENNReal.ofReal_pos] at hx'
  exact hx'.le

lemma rightDerivStieltjes_of_neg {x : ℝ} (hx : x < 0) :
    f.rightDerivStieltjes x = ⊥ :=
  rightDerivStieltjes_of_lt_xmin (hx.trans_le ENNReal.toReal_nonneg)

lemma rightDerivStieltjes_eq_bot_iff {x : ℝ} :
    f.rightDerivStieltjes x = ⊥ ↔ x < f.xmin.toReal := by
  refine ⟨fun h ↦ ?_, fun h ↦ rightDerivStieltjes_of_lt_xmin h⟩
  sorry

lemma rightDerivStieltjes_eq_top_iff {x : ℝ} :
    f.rightDerivStieltjes x = ⊤ ↔ f.xmax ≤ ENNReal.ofReal x := by
  refine ⟨fun h ↦ ?_, fun h ↦ rightDerivStieltjes_of_ge_xmax h⟩
  sorry

lemma rightDerivStieltjes_of_ne_top (hf : ∀ x, 0 < x → f x ≠ ∞) (x : ℝ) :
    f.rightDerivStieltjes x = Function.rightLim (fun y ↦ (rightDeriv f.realFun y : EReal)) x := by
  sorry

lemma rightDerivStieltjes_ne_top (hf : ∀ x, 0 < x → f x ≠ ∞) (x : ℝ) :
    f.rightDerivStieltjes x ≠ ⊤ := by
  sorry

@[simp]
lemma rightDerivStieltjes_one : f.rightDerivStieltjes 1 = rightDeriv f.realFun 1 := by
  sorry

@[simp]
lemma toReal_max_xmin : (max f.xmin g.xmin).toReal = max f.xmin.toReal g.xmin.toReal := by
  sorry

lemma rightDerivStieltjes_add :
    (f + g).rightDerivStieltjes = f.rightDerivStieltjes + g.rightDerivStieltjes := by
  ext x
  by_cases hf_top : f.rightDerivStieltjes x = ⊤
  · rw [ERealStieltjes.add_apply_of_eq_top_left hf_top]
    simp only [rightDerivStieltjes_eq_top_iff, xmax_add, min_le_iff]
    left
    rwa [rightDerivStieltjes_eq_top_iff] at hf_top
  by_cases hg_top : g.rightDerivStieltjes x = ⊤
  · rw [ERealStieltjes.add_apply_of_eq_top_right hg_top]
    simp only [rightDerivStieltjes_eq_top_iff, xmax_add, min_le_iff]
    right
    rwa [rightDerivStieltjes_eq_top_iff] at hg_top
  rw [ERealStieltjes.add_apply_of_ne_top hf_top hg_top]
  have hx_lt_f : ENNReal.ofReal x < f.xmax := by
    rw [rightDerivStieltjes_eq_top_iff] at hf_top
    simpa using hf_top
  have hx_lt_g : ENNReal.ofReal x < g.xmax := by
    rw [rightDerivStieltjes_eq_top_iff] at hg_top
    simpa using hg_top
  simp only [DivFunction.rightDerivStieltjes, xmin_add, toReal_max_xmin, lt_max_iff, xmax_add,
    min_le_iff, not_le.mpr hx_lt_f, not_le.mpr hx_lt_g, or_self, ↓reduceIte]
  by_cases hx_fmin : x < f.xmin.toReal
  · simp [hx_fmin]
  by_cases hx_gmin : x < g.xmin.toReal
  · simp [hx_gmin]
  simp only [hx_fmin, hx_gmin, or_self, ↓reduceIte]
  sorry

end RightDeriv

section DerivAtTop

noncomputable
def derivAtTop (f : DivFunction) : ℝ≥0∞ := (limsup f.rightDerivStieltjes atTop).toENNReal

lemma tendsto_rightDerivStieltjes_atTop :
    Tendsto f.rightDerivStieltjes atTop (𝓝 f.derivAtTop) := by
  rw [derivAtTop, EReal.coe_toENNReal]
  · sorry
  · sorry

@[simp]
lemma derivAtTop_zero : derivAtTop (0 : DivFunction) = 0 := sorry

lemma derivAtTop_congr (h : f =ᶠ[atTop] g) : f.derivAtTop = g.derivAtTop := by
  sorry
  --refine limsup_congr ?_
  --filter_upwards [h] with x hx
  --rw [hx]

lemma derivAtTop_congr_nonneg (h : ∀ x, f x = g x) : f.derivAtTop = g.derivAtTop :=
  derivAtTop_congr (.of_forall h)

lemma tendsto_derivAtTop : Tendsto (fun x ↦ f x / x) atTop (𝓝 f.derivAtTop) := by
  sorry

@[simp]
lemma derivAtTop_add : (f + g).derivAtTop = f.derivAtTop + g.derivAtTop := by
  suffices Tendsto (fun x ↦ (f + g) x / x) atTop (𝓝 (f.derivAtTop + g.derivAtTop)) from
    tendsto_nhds_unique tendsto_derivAtTop this
  simp only [add_apply]
  sorry

@[simp]
lemma derivAtTop_smul {c : ℝ≥0} : (c • f).derivAtTop = c * f.derivAtTop := sorry

lemma le_add_derivAtTop {x y : ℝ≥0∞} (hyx : y ≤ x) :
    f x ≤ f y + f.derivAtTop * (x - y) := by
  sorry

lemma le_add_derivAtTop'' (x y : ℝ≥0∞) :
    f (x + y) ≤ f x + f.derivAtTop * y := by
  sorry

lemma le_add_derivAtTop' (x : ℝ≥0∞) {u : ℝ≥0∞} (hu' : u ≤ 1) :
    f x ≤ f (x * u) + f.derivAtTop * x * (1 - u) := by
  have : x = x * u + x * (1 - u) := by
    rw [← mul_add]
    rw [add_tsub_cancel_of_le hu', mul_one]
  conv_lhs => rw [this]
  refine (le_add_derivAtTop'' (x * u) (x * (1 - u))).trans ?_
  rw [mul_assoc]

lemma lintegral_comp_rnDeriv_ne_top (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hf_zero : f 0 ≠ ∞) (hf_deriv : f.derivAtTop ≠ ∞) :
    ∫⁻ x, f (μ.rnDeriv ν x) ∂ν ≠ ∞ := by
  sorry
  -- obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, _ → c * x + c' ≤ (f x).toReal :=
  --   f.convexOn_toReal.exists_affine_le (convex_Ici 0)
  -- refine integrable_of_le_of_le (f := fun x ↦ f (μ.rnDeriv ν x).toReal)
  --   (g₁ := fun x ↦ c * (μ.rnDeriv ν x).toReal + c')
  --   (g₂ := fun x ↦ (derivAtTop f).toReal * (μ.rnDeriv ν x).toReal + f 0)
  --   ?_ ?_ ?_ ?_ ?_
  -- · exact (hf.comp_measurable (μ.measurable_rnDeriv ν).ennreal_toReal).aestronglyMeasurable
  -- · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  -- · refine ae_of_all _ (fun x ↦ ?_)
  --   have h := le_add_derivAtTop'' hf_cvx hf_deriv le_rfl
  --     (ENNReal.toReal_nonneg : 0 ≤ (μ.rnDeriv ν x).toReal)
  --   rwa [zero_add, add_comm] at h
  -- · refine (Integrable.const_mul ?_ _).add (integrable_const _)
  --   exact Measure.integrable_toReal_rnDeriv
  -- · refine (Integrable.const_mul ?_ _).add (integrable_const _)
  --   exact Measure.integrable_toReal_rnDeriv

end DerivAtTop

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

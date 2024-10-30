/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
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

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

structure DivFunction where
  toFun : ℝ≥0∞ → ℝ≥0∞
  one : toFun 1 = 0
  rightDerivOne : rightDeriv (fun x : ℝ ↦ (toFun (ENNReal.ofReal x)).toReal) 1 = 0
  convexOn' : ConvexOn ℝ≥0 univ toFun
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

lemma monotoneOn : MonotoneOn f (Ici 1) := sorry

lemma antitoneOn : AntitoneOn f (Iic 1) := sorry

end Def

variable {f g : DivFunction}

noncomputable def xmin (f : DivFunction) : ℝ≥0∞ := sInf {x | f x ≠ ∞}
noncomputable def xmax (f : DivFunction) : ℝ≥0∞ := sSup {x | f x ≠ ∞}

lemma xmin_lt_one : f.xmin < 1 := by
  rw [xmin, sInf_lt_iff]
  sorry

lemma xmin_lt_top : f.xmin < ∞ := lt_top_of_lt xmin_lt_one

lemma xmin_ne_top : f.xmin ≠ ∞ := xmin_lt_top.ne

lemma one_lt_xmax : 1 < f.xmax := by
  rw [xmax, lt_sSup_iff]
  sorry

lemma xmax_pos : 0 < f.xmax := zero_lt_one.trans one_lt_xmax

lemma eq_top_of_lt_xmin {x : ℝ≥0∞} (hx_lt : x < f.xmin) : f x = ∞ := by
  rw [xmin] at hx_lt
  by_contra h_eq
  exact not_le_of_lt hx_lt (sInf_le h_eq)

lemma eq_top_of_xmax_lt {x : ℝ≥0∞} (hx_gt : f.xmax < x) : f x = ∞ := by
  rw [xmax] at hx_gt
  by_contra h_eq
  exact not_le_of_lt hx_gt (le_sSup h_eq)

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
    have h_ne_bot : (𝓝[<] f.xmin).NeBot := sorry
    refine tendsto_nhds_unique ?_ this
    sorry
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  sorry

lemma apply_xmax_eq_top (h : f.xmax ≠ ∞) : f f.xmax = ∞ := by
  suffices Tendsto f (𝓝[>] f.xmin) (𝓝 ∞) by
    have h_ne_bot : (𝓝[>] f.xmin).NeBot := sorry
    refine tendsto_nhds_unique ?_ this
    sorry
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  sorry

protected def zero : DivFunction where
  toFun := 0
  one := rfl
  rightDerivOne := by simp
  convexOn' := convexOn_const _ convex_univ
  continuous' := continuous_const

protected noncomputable def add (f g : DivFunction) : DivFunction where
  toFun := fun x ↦ f x + g x
  one := by simp
  rightDerivOne := by
    simp only [Pi.add_apply]
    sorry
  convexOn' := sorry
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
instance : Module ℝ≥0 DivFunction where
  smul c f := {
    toFun := fun x ↦ c * f x
    one := sorry
    rightDerivOne := sorry
    convexOn' := sorry
    continuous' := sorry}
  one_smul _ := ext fun _ ↦ one_mul _
  mul_smul _ _ _ := ext fun _ ↦ sorry  -- mul_assoc _ _ _
  smul_zero _ := ext fun _ ↦ mul_zero _
  smul_add _ _ _ := ext fun _ ↦ mul_add _ _ _
  add_smul _ _ _ := ext fun _ ↦ sorry  -- add_mul _ _ _
  zero_smul _ := ext fun _ ↦ zero_mul _

@[simp] lemma smul_apply (c : ℝ≥0) (f : DivFunction) (x : ℝ≥0∞) : (c • f) x = c * f x := rfl

section RealFun
variable (f : DivFunction)

noncomputable
def realFun : ℝ → ℝ := (fun x : ℝ ↦ (f (ENNReal.ofReal x)).toReal)

@[simp] lemma rightDeriv_one : rightDeriv f.realFun 1 = 0 :=
  f.rightDerivOne

@[simp]
lemma realFun_of_nonpos {x : ℝ} (hx : x ≤ 0) : f.realFun x = f.realFun 0 := by
  simp [realFun, ENNReal.ofReal_of_nonpos hx]

lemma realFun_of_lt_xmin {x : ℝ} (hx : ENNReal.ofReal x < f.xmin) : f.realFun x = 0 := by
  simp [realFun, eq_top_of_lt_xmin hx]

lemma realFun_of_xmax_lt {x : ℝ} (hx : f.xmax < ENNReal.ofReal x) : f.realFun x = 0 := by
  simp [realFun, eq_top_of_xmax_lt hx]

lemma continuousOn_realFun_Ioo : ContinuousOn f.realFun (Ioo f.xmin.toReal f.xmax.toReal) := by
  by_cases h : f.xmax = ∞
  · simp [h]
  refine ENNReal.continuousOn_toReal.comp
    (f.continuous.comp_continuousOn ENNReal.continuous_ofReal.continuousOn) fun x hx ↦ ?_
  refine (lt_top_of_mem_Ioo ?_).ne
  rw [mem_Ioo, ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top, ENNReal.ofReal_lt_iff_lt_toReal ?_ h]
  · exact hx
  · exact ENNReal.toReal_nonneg.trans hx.1.le

lemma continuousOn_realFun_Ioi (h : f.xmax = ∞) :
    ContinuousOn f.realFun (Ioi f.xmin.toReal) := by
  refine ENNReal.continuousOn_toReal.comp
    (f.continuous.comp_continuousOn ENNReal.continuous_ofReal.continuousOn) fun x hx ↦ ?_
  refine (lt_top_of_mem_Ioo ?_).ne
  simp only [h, mem_Ioo, ENNReal.ofReal_lt_top, and_true]
  rw [ENNReal.lt_ofReal_iff_toReal_lt xmin_ne_top]
  exact hx

lemma continuousOn_realFun_Ici (h : ∀ x, f x ≠ ∞) : ContinuousOn f.realFun (Ici 0) :=
  ENNReal.continuousOn_toReal.comp
    (f.continuous.comp_continuousOn ENNReal.continuous_ofReal.continuousOn) fun _ _ ↦ h _

lemma convexOn_Ioo_realFun : ConvexOn ℝ (Ioo f.xmin.toReal f.xmax.toReal) f.realFun := sorry

lemma convexOn_Ici_realFun (h : ∀ x, f x ≠ ∞) : ConvexOn ℝ (Ici 0) f.realFun := sorry

end RealFun

section RightDeriv

protected noncomputable def rightDeriv (f : DivFunction) : ERealStieltjes where
  toFun := fun x ↦
    if x < f.xmin.toReal then ⊥
    else if f.xmax ≤ ENNReal.ofReal x then ⊤
    else rightDeriv f.realFun x
  mono' := sorry
  right_continuous' := sorry

end RightDeriv

section DerivAtTop

noncomputable
def derivAtTop (f : DivFunction) : ℝ≥0∞ := limsup (fun x ↦ f x / x) atTop

-- lemma derivAtTop_eq_rightDeriv :

@[simp]
lemma derivAtTop_zero : derivAtTop (0 : DivFunction) = 0 := by simp [derivAtTop]

lemma derivAtTop_congr (h : f =ᶠ[atTop] g) : f.derivAtTop = g.derivAtTop := by
  refine limsup_congr ?_
  filter_upwards [h] with x hx
  rw [hx]

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

lemma lintegral_comp_rnDeriv_ne_top (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hf_deriv : f.derivAtTop ≠ ∞) :
    ∫⁻ x, f (μ.rnDeriv ν x).toReal ∂ν ≠ ∞ := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, _ → c * x + c' ≤ (f x).toReal :=
    f.convexOn_toReal.exists_affine_le (convex_Ici 0)
  sorry
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

end ProbabilityTheory

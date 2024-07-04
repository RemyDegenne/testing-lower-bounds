/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Testing.Binary
import TestingLowerBounds.FDiv.Basic
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Convex.Deriv
import TestingLowerBounds.ForMathlib.MonotoneOnTendsto


open Set Filter Topology

open scoped ENNReal NNReal

variable {f : ℝ → ℝ}

/-- The right derivative of a real function. -/
noncomputable
def rightDeriv (f : ℝ → ℝ) : ℝ → ℝ := fun x ↦ derivWithin f (Ioi x) x

lemma rightDeriv_def (f : ℝ → ℝ) (x : ℝ) : rightDeriv f x = derivWithin f (Ioi x) x := rfl

/-- The left derivative of a real function. -/
noncomputable
def leftDeriv (f : ℝ → ℝ) : ℝ → ℝ := fun x ↦ derivWithin f (Iio x) x

lemma leftDeriv_def (f : ℝ → ℝ) (x : ℝ) : leftDeriv f x = derivWithin f (Iio x) x := rfl

lemma rightDeriv_eq_leftDeriv_apply (f : ℝ → ℝ) (x : ℝ) :
    rightDeriv f x = - leftDeriv (fun x ↦ f (-x)) (-x) := by
  change rightDeriv f x = -leftDeriv (f ∘ Neg.neg) (-x)
  have h_map : MapsTo Neg.neg (Iio (-x)) (Ioi x) := fun _ (h : _ < -x) ↦ lt_neg_of_lt_neg h
  have h_map' : MapsTo Neg.neg (Ioi x) (Iio (-x)) := fun _ (h : x < _) ↦ neg_lt_neg h
  by_cases hf_diff : DifferentiableWithinAt ℝ f (Ioi x) x
  swap
  · rw [rightDeriv_def, leftDeriv_def, derivWithin_zero_of_not_differentiableWithinAt hf_diff,
      derivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    contrapose! hf_diff
    convert DifferentiableWithinAt.comp x hf_diff ((differentiable_neg _).differentiableWithinAt)
      h_map' using 1
    simp [Function.comp.assoc]
  simp_rw [leftDeriv]
  rw [derivWithin.comp _ ((neg_neg x).symm ▸ hf_diff) (differentiable_neg _).differentiableWithinAt
    h_map (uniqueDiffWithinAt_Iio (-x)), neg_neg, ← rightDeriv_def, derivWithin_neg]
  swap; · exact uniqueDiffWithinAt_Iio _
  simp only [mul_neg, mul_one, neg_neg]

lemma rightDeriv_eq_leftDeriv (f : ℝ → ℝ) :
    rightDeriv f = fun x ↦ - leftDeriv (fun y ↦ f (-y)) (-x) := by
  ext x
  simp [rightDeriv_eq_leftDeriv_apply]

lemma leftDeriv_eq_rightDeriv_apply (f : ℝ → ℝ) (x : ℝ) :
    leftDeriv f x = - rightDeriv (fun y ↦ f (-y)) (-x) := by
  simp [rightDeriv_eq_leftDeriv_apply, Function.comp.assoc]

lemma leftDeriv_eq_rightDeriv (f : ℝ → ℝ) :
    leftDeriv f = fun x ↦ - rightDeriv (fun y ↦ f (-y)) (-x) := by
  ext x
  simp [leftDeriv_eq_rightDeriv_apply]

namespace ConvexOn

section Slope

lemma bddBelow_slope_Ioi (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    BddBelow (slope f x '' Ioi x) := by
  refine bddBelow_iff_subset_Ici.mpr ⟨(slope f x (x - 1)), fun y ⟨z, (hz : x < z), hz'⟩ ↦ ?_⟩
  simp_rw [mem_Ici, ← hz']
  exact slope_mono hfc trivial (by simp) ⟨trivial, hz.ne'⟩ (by linarith)

lemma bddAbove_slope_Iio (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    BddAbove (slope f x '' Iio x) := by
  refine bddAbove_iff_subset_Iic.mpr ⟨(slope f x (x + 1)), fun y ⟨z, (hz : z < x), hz'⟩ ↦ ?_⟩
  simp_rw [mem_Iic, ← hz']
  exact slope_mono hfc (mem_univ x) ⟨trivial, hz.ne⟩ (by simp) (by linarith)

end Slope

-- TODO: this can be generalized to a set S, where the function is convex, but I still need to figure out what hp to require, since the minimal assumption I think is that there exist a right interval of x that is contained in S (so x itself does not have to be in S), i.e. (x, y) ⊆ S, I don't know if. To generalize we will need MonotoneOn.tendsto_nhdsWithin_Ioo_right. However there are dirrerent kinds of sufficient conditions that could be given, for example S open and x in S or x in the interior of S. Discuss this with Remy. Maybe the minimal hp I described is not sufficient, I also need to assure some kind of boundedness of the slope, this should be assured if x is in the interior of S, because then we can take a point to the left of x but still inside S and use the monotonicity of the solpe in S, but can we do better? For now we can leave it like this
lemma hasRightDerivAt (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    HasDerivWithinAt f (sInf (slope f x '' Ioi x)) (Ioi x) x := by
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, diff_singleton_eq_self]
  have h_mono : MonotoneOn (slope f x) (Ioi x) := by
    refine monotoneOn_iff_forall_lt.mpr fun y (hy : x < y) z (hz : x < z) hz' ↦ ?_
    simp_rw [slope_def_field]
    exact hfc.secant_mono trivial trivial trivial hy.ne' hz.ne' hz'.le
  exact MonotoneOn.tendsto_nhdsWithin_Ioi h_mono (bddBelow_slope_Ioi hfc x)

lemma differentiableWithinAt_Ioi (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    DifferentiableWithinAt ℝ f (Ioi x) x :=
  (hfc.hasRightDerivAt x).differentiableWithinAt

lemma hadDerivWithinAt_rightDeriv (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    HasDerivWithinAt f (rightDeriv f x) (Ioi x) x :=
  (hfc.differentiableWithinAt_Ioi x).hasDerivWithinAt

lemma hasLeftDerivAt (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    HasDerivWithinAt f (sSup (slope f x '' Iio x)) (Iio x) x := by
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Iio, lt_self_iff_false, not_false_eq_true, diff_singleton_eq_self]
  have h_mono : MonotoneOn (slope f x) (Iio x) := by
    refine monotoneOn_iff_forall_lt.mpr fun y (hy : y < x) z (hz : z < x) hz' ↦ ?_
    simp_rw [slope_def_field]
    exact hfc.secant_mono trivial trivial trivial hy.ne hz.ne hz'.le
  exact MonotoneOn.tendsto_nhdsWithin_Iio h_mono (bddAbove_slope_Iio hfc x)

lemma differentiableWithinAt_Iio (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    DifferentiableWithinAt ℝ f (Iio x) x :=
  (hfc.hasLeftDerivAt x).differentiableWithinAt

lemma hadDerivWithinAt_leftDeriv (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    HasDerivWithinAt f (leftDeriv f x) (Iio x) x :=
  (hfc.differentiableWithinAt_Iio x).hasDerivWithinAt

lemma rightDeriv_eq_sInf_slope (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    rightDeriv f x = sInf (slope f x '' Ioi x) :=
  (hfc.hasRightDerivAt x).derivWithin (uniqueDiffWithinAt_Ioi x)

lemma leftDeriv_eq_sSup_slope (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    leftDeriv f x = sSup (slope f x '' Iio x) :=
  (hfc.hasLeftDerivAt x).derivWithin (uniqueDiffWithinAt_Iio x)

lemma rightDeriv_mono (hfc : ConvexOn ℝ univ f) : Monotone (rightDeriv f) := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [hfc.rightDeriv_eq_sInf_slope]
  refine csInf_le_of_le (b := slope f x y) (bddBelow_slope_Ioi hfc x)
    ⟨y, by simp [hxy]⟩ (le_csInf nonempty_of_nonempty_subtype ?_)
  rintro _ ⟨z, (yz : y < z), rfl⟩
  rw [slope_comm]
  exact slope_mono hfc trivial ⟨trivial, hxy.ne⟩ ⟨trivial, yz.ne'⟩ (hxy.trans yz).le

lemma leftDeriv_mono (hfc : ConvexOn ℝ univ f) : Monotone (leftDeriv f) := by
  rw [leftDeriv_eq_rightDeriv]
  change Monotone (- rightDeriv (f ∘ Neg.neg) ∘ Neg.neg)
  refine (Monotone.comp_antitone ?_ fun _ _ h ↦ neg_le_neg_iff.mpr h).neg
  exact hfc.comp_neg.rightDeriv_mono

lemma leftDeriv_le_rightDeriv (hfc : ConvexOn ℝ univ f) : leftDeriv f ≤ rightDeriv f := by
  intro x
  rw [hfc.rightDeriv_eq_sInf_slope, hfc.leftDeriv_eq_sSup_slope]
  refine csSup_le nonempty_of_nonempty_subtype ?_
  rintro _ ⟨z, (zx : z < x), rfl⟩
  refine le_csInf nonempty_of_nonempty_subtype ?_
  rintro _ ⟨y, (xy : x < y), rfl⟩
  exact slope_mono hfc trivial ⟨trivial, zx.ne⟩ ⟨trivial, xy.ne'⟩ (zx.trans xy).le

lemma rightDeriv_right_continuous (hfc : ConvexOn ℝ univ f) (w : ℝ) :
    ContinuousWithinAt (rightDeriv f) (Ici w) w := by
  simp_rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
  have h_lim := MonotoneOn.tendsto_nhdsWithin_Ioi (hfc.rightDeriv_mono.monotoneOn (Ioi w))
    (Monotone.map_bddBelow hfc.rightDeriv_mono bddBelow_Ioi)
  set l := sInf (rightDeriv f '' Ioi w)
  convert h_lim
  apply le_antisymm
  · exact ge_of_tendsto h_lim <| eventually_nhdsWithin_of_forall
      fun y (hy : w < y) ↦ hfc.rightDeriv_mono hy.le
  · rw [hfc.rightDeriv_eq_sInf_slope]
    refine le_csInf nonempty_of_nonempty_subtype ?_ --is there any way to avoid the rintro here? if I just use fun inside the refine it does not work, it seems that the rfl inside the pattern is not supported by the refine tactic
    rintro _ ⟨y, (wy : w < y), rfl⟩
    have slope_lim : Tendsto (slope f y) (𝓝[>] w) (𝓝 (slope f y w)) := by
      have hf_cont : ContinuousWithinAt f (Ioi w) w := -- I would like to replace this with a lemma that derives the continuity from the convexity, it seems that this result is still not in mathlib, see https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Continuity.20.20of.20convex.20functions, they are in the process of proving it in the LeanCamCombi project
        DifferentiableWithinAt.continuousWithinAt (hfc.differentiableWithinAt_Ioi w)
      exact ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀ (sub_ne_zero.2 wy.ne)).smul
        (hf_cont.sub continuousWithinAt_const) |>.tendsto
    rw [slope_comm] at slope_lim
    refine le_of_tendsto_of_tendsto h_lim slope_lim ?_
    rw [← nhdsWithin_Ioo_eq_nhdsWithin_Ioi wy]
    refine eventually_nhdsWithin_of_forall fun z hz ↦ ?_
    rw [slope_comm, hfc.rightDeriv_eq_sInf_slope]
    exact csInf_le (bddBelow_slope_Ioi hfc z) ⟨y, hz.2, rfl⟩

lemma leftDeriv_left_continuous (hfc : ConvexOn ℝ univ f) (w : ℝ) :
    ContinuousWithinAt (leftDeriv f) (Iic w) w := by
  have h_map : MapsTo Neg.neg (Iic w) (Ici (-w)) := fun _ (h : _ ≤ w) ↦ (neg_le_neg_iff.mpr h)
  rw [leftDeriv_eq_rightDeriv]
  exact (hfc.comp_neg.rightDeriv_right_continuous _).comp continuousWithinAt_neg h_map |>.neg

/-- The right derivative of a convex real function is a Stieltjes function. -/
noncomputable
def rightDerivStieltjes {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    StieltjesFunction where
  toFun := rightDeriv f
  mono' _ _ := fun h ↦ hf.rightDeriv_mono h
  right_continuous' _ := hf.rightDeriv_right_continuous _

end ConvexOn

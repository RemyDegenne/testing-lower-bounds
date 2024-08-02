/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Convex
import TestingLowerBounds.ForMathlib.MonotoneOnTendsto
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Measure.Stieltjes


open Set Filter Topology

open scoped ENNReal NNReal

variable {f : ℝ → ℝ} {x : ℝ}

/-- The right derivative of a real function. -/
noncomputable
def rightDeriv (f : ℝ → ℝ) : ℝ → ℝ := fun x ↦ derivWithin f (Ioi x) x

lemma rightDeriv_def (f : ℝ → ℝ) (x : ℝ) : rightDeriv f x = derivWithin f (Ioi x) x := rfl

/-- The left derivative of a real function. -/
noncomputable
def leftDeriv (f : ℝ → ℝ) : ℝ → ℝ := fun x ↦ derivWithin f (Iio x) x

lemma leftDeriv_def (f : ℝ → ℝ) (x : ℝ) : leftDeriv f x = derivWithin f (Iio x) x := rfl

lemma rightDeriv_of_not_differentiableWithinAt {f : ℝ → ℝ} {x : ℝ}
    (hf : ¬DifferentiableWithinAt ℝ f (Ioi x) x) :
    rightDeriv f x = 0 := by
  rw [rightDeriv_def, derivWithin_zero_of_not_differentiableWithinAt hf]

lemma leftDeriv_of_not_differentiableWithinAt {f : ℝ → ℝ} {x : ℝ}
    (hf : ¬DifferentiableWithinAt ℝ f (Iio x) x) :
    leftDeriv f x = 0 := by
  rw [leftDeriv_def, derivWithin_zero_of_not_differentiableWithinAt hf]

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

lemma Filter.EventuallyEq.derivWithin_eq_nhds {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f₁ f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}
    (h : f₁ =ᶠ[𝓝 x] f) :
    derivWithin f₁ s x = derivWithin f s x := by
  simp_rw [derivWithin]
  rw [Filter.EventuallyEq.fderivWithin_eq_nhds h]

lemma Filter.EventuallyEq.rightDeriv_eq_nhds {x : ℝ} {g : ℝ → ℝ} (h : f =ᶠ[𝓝 x] g) :
    rightDeriv f x = rightDeriv g x := h.derivWithin_eq_nhds

lemma rightDeriv_congr_atTop {g : ℝ → ℝ} (h : f =ᶠ[atTop] g) :
    rightDeriv f =ᶠ[atTop] rightDeriv g := by
  have h' : ∀ᶠ x in atTop, f =ᶠ[𝓝 x] g := by
    -- todo: replace by clean filter proof?
    simp only [Filter.EventuallyEq, eventually_atTop, ge_iff_le] at h ⊢
    obtain ⟨a, ha⟩ := h
    refine ⟨a + 1, fun b hab ↦ ?_⟩
    have h_ge : ∀ᶠ x in 𝓝 b, a ≤ x := eventually_ge_nhds ((lt_add_one _).trans_le hab)
    filter_upwards [h_ge] using ha
  filter_upwards [h'] with a ha using ha.rightDeriv_eq_nhds

@[simp]
lemma rightDeriv_zero : rightDeriv 0 = 0 := by
  ext x
  simp only [rightDeriv, Pi.zero_apply]
  exact derivWithin_const x _ 0 (uniqueDiffWithinAt_Ioi x)

@[simp]
lemma rightDeriv_const (c : ℝ) : rightDeriv (fun _ ↦ c) = 0 := by
  ext x
  rw [rightDeriv_def, Pi.zero_apply]
  exact derivWithin_const x _ c (uniqueDiffWithinAt_Ioi x)

@[simp]
lemma leftDeriv_const (c : ℝ) : leftDeriv (fun _ ↦ c) = 0 := by
  simp_rw [leftDeriv_eq_rightDeriv, rightDeriv_const, Pi.zero_apply, neg_zero]
  rfl

@[simp]
lemma rightDeriv_const_mul (a : ℝ) {f : ℝ → ℝ} :
    rightDeriv (fun x ↦ a * f x) = fun x ↦ a * rightDeriv f x := by
  ext x
  by_cases ha : a = 0
  · simp [ha]
  by_cases hfx : DifferentiableWithinAt ℝ f (Ioi x) x
  · simp_rw [rightDeriv_def, derivWithin_const_mul (uniqueDiffWithinAt_Ioi x) _ hfx]
  · rw [rightDeriv_of_not_differentiableWithinAt hfx, mul_zero,
      rightDeriv_of_not_differentiableWithinAt]
    have : f = fun x ↦ a⁻¹ * (a * f x) := by ext; simp [ha]
    exact fun h_diff ↦ hfx <| this ▸ h_diff.const_mul _

@[simp]
lemma leftDeriv_const_mul (a : ℝ) {f : ℝ → ℝ} :
    leftDeriv (fun x ↦ a * f x) = fun x ↦ a * leftDeriv f x := by
  simp_rw [leftDeriv_eq_rightDeriv, rightDeriv_const_mul, neg_mul_eq_mul_neg]

@[simp]
lemma rightDeriv_neg {f : ℝ → ℝ} : rightDeriv (fun x ↦ - f x) = fun x ↦ - rightDeriv f x := by
  simp_rw [← neg_one_mul (f _), rightDeriv_const_mul, neg_one_mul]

@[simp]
lemma leftDeriv_neg {f : ℝ → ℝ} : leftDeriv (fun x ↦ - f x) = fun x ↦ - leftDeriv f x := by
  simp [leftDeriv_eq_rightDeriv]

@[simp]
lemma rightDeriv_id : rightDeriv id = fun _ ↦ 1 := by
  ext x
  rw [rightDeriv_def, derivWithin_id _ _ (uniqueDiffWithinAt_Ioi x)]

@[simp]
lemma rightDeriv_id' : rightDeriv (fun x ↦ x) = fun _ ↦ 1 := rightDeriv_id

@[simp]
lemma leftDeriv_id : leftDeriv id = fun _ ↦ 1 := by
  ext x
  rw [leftDeriv_def, derivWithin_id _ _ (uniqueDiffWithinAt_Iio x)]

@[simp]
lemma leftDeriv_id' : leftDeriv (fun x ↦ x) = fun _ ↦ 1 := leftDeriv_id

lemma rightDeriv_add_apply {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableWithinAt ℝ f (Ioi x) x)
    (hg : DifferentiableWithinAt ℝ g (Ioi x) x) :
    rightDeriv (f + g) x = rightDeriv f x + rightDeriv g x := by
  simp_rw [rightDeriv_def, ← derivWithin_add (uniqueDiffWithinAt_Ioi x) hf hg]
  rfl

lemma rightDeriv_add_apply' {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableWithinAt ℝ f (Ioi x) x)
    (hg : DifferentiableWithinAt ℝ g (Ioi x) x) :
    rightDeriv (fun x ↦ f x + g x) x = rightDeriv f x + rightDeriv g x :=
  rightDeriv_add_apply hf hg

lemma rightDeriv_add {f g : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Ioi x) x)
    (hg : ∀ x, DifferentiableWithinAt ℝ g (Ioi x) x) :
    rightDeriv (f + g) = fun x ↦ rightDeriv f x + rightDeriv g x := by
  ext x; exact rightDeriv_add_apply (hf x) (hg x)

lemma rightDeriv_add' {f g : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Ioi x) x)
    (hg : ∀ x, DifferentiableWithinAt ℝ g (Ioi x) x) :
    rightDeriv (fun x ↦ f x + g x) = fun x ↦ rightDeriv f x + rightDeriv g x := by
  simp_rw [← Pi.add_apply f g, rightDeriv_add hf hg]

lemma leftDeriv_add_apply {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableWithinAt ℝ f (Iio x) x)
    (hg : DifferentiableWithinAt ℝ g (Iio x) x) :
    leftDeriv (f + g) x = leftDeriv f x + leftDeriv g x := by
  simp_rw [leftDeriv_def, ← derivWithin_add (uniqueDiffWithinAt_Iio x) hf hg]
  rfl

lemma leftDeriv_add {f g : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Iio x) x)
    (hg : ∀ x, DifferentiableWithinAt ℝ g (Iio x) x) :
    leftDeriv (f + g) = fun x ↦ leftDeriv f x + leftDeriv g x := by
  ext x; exact leftDeriv_add_apply (hf x) (hg x)

lemma leftDeriv_add' {f g : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Iio x) x)
    (hg : ∀ x, DifferentiableWithinAt ℝ g (Iio x) x) :
    leftDeriv (fun x ↦ f x + g x) = fun x ↦ leftDeriv f x + leftDeriv g x := by
  simp_rw [← Pi.add_apply f g, leftDeriv_add hf hg]

lemma rightDeriv_add_const {f : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Ioi x) x) (c : ℝ) :
    rightDeriv (fun x ↦ f x + c) = rightDeriv f := by
  simp [rightDeriv_add' hf (fun _ ↦ differentiableWithinAt_const c)]

lemma leftDeriv_add_const {f : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Iio x) x) (c : ℝ) :
    leftDeriv (fun x ↦ f x + c) = leftDeriv f := by
  simp [leftDeriv_add' hf (fun _ ↦ differentiableWithinAt_const c)]

lemma rightDeriv_add_linear {f : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Ioi x) x) (a : ℝ) :
    rightDeriv (fun x ↦ f x + a * x) = rightDeriv f + fun _ ↦ a := by
  rw [rightDeriv_add' hf (by fun_prop), rightDeriv_const_mul, rightDeriv_id']
  ext; simp

lemma leftDeriv_add_linear {f : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Iio x) x) (a : ℝ) :
    leftDeriv (fun x ↦ f x + a * x) = leftDeriv f + fun _ ↦ a := by
  rw [leftDeriv_add' hf (by fun_prop), leftDeriv_const_mul, leftDeriv_id']
  ext; simp


namespace ConvexOn

section Slope

lemma bddBelow_slope_Ioi (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    BddBelow (slope f x '' Ioi x) := by
  refine bddBelow_iff_subset_Ici.mpr ⟨(slope f x (x - 1)), fun y ⟨z, (hz : x < z), hz'⟩ ↦ ?_⟩
  simp_rw [mem_Ici, ← hz']
  exact slope_mono hfc trivial (by simp) ⟨trivial, hz.ne'⟩ (by linarith)

lemma bddBelow_slope_Ioi' (hfc : ConvexOn ℝ (Ici 0) f) (x : ℝ) (hx : 0 < x) :
    BddBelow (slope f x '' Ioi x) := by
  refine bddBelow_iff_subset_Ici.mpr ⟨(slope f x 0), fun y ⟨z, (hz : x < z), hz'⟩ ↦ ?_⟩
  simp_rw [mem_Ici, ← hz']
  exact slope_mono hfc hx.le (by simp [hx.ne]) ⟨(hx.trans hz).le, hz.ne'⟩ (by linarith)

lemma bddAbove_slope_Iio (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    BddAbove (slope f x '' Iio x) := by
  refine bddAbove_iff_subset_Iic.mpr ⟨(slope f x (x + 1)), fun y ⟨z, (hz : z < x), hz'⟩ ↦ ?_⟩
  simp_rw [mem_Iic, ← hz']
  exact slope_mono hfc (mem_univ x) ⟨trivial, hz.ne⟩ (by simp) (by linarith)

end Slope

-- TODO: this can be generalized to a set S, where the function is convex,
-- but I still need to figure out what hp to require,
-- since the minimal assumption I think is that there exist a right interval of x
-- that is contained in S (so x itself does not have to be in S), i.e. (x, y) ⊆ S, I don't know if.
-- To generalize we will need MonotoneOn.tendsto_nhdsWithin_Ioo_right.
-- However there are dirrerent kinds of sufficient conditions that could be given,
-- for example S open and x in S or x in the interior of S. Discuss this with Remy.
-- Maybe the minimal hp I described is not sufficient, I also need to assure some kind
-- of boundedness of the slope, this should be assured if x is in the interior of S,
-- because then we can take a point to the left of x but still inside S and use the monotonicity
-- of the solpe in S, but can we do better? For now we can leave it like this
lemma hasRightDerivAt (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    HasDerivWithinAt f (sInf (slope f x '' Ioi x)) (Ioi x) x := by
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, diff_singleton_eq_self]
  have h_mono : MonotoneOn (slope f x) (Ioi x) := by
    refine monotoneOn_iff_forall_lt.mpr fun y (hy : x < y) z (hz : x < z) hz' ↦ ?_
    simp_rw [slope_def_field]
    exact hfc.secant_mono trivial trivial trivial hy.ne' hz.ne' hz'.le
  exact MonotoneOn.tendsto_nhdsWithin_Ioi h_mono (bddBelow_slope_Ioi hfc x)

lemma hasRightDerivAt' (hfc : ConvexOn ℝ (Ici 0) f) (hx : 0 < x) :
    HasDerivWithinAt f (sInf (slope f x '' Ioi x)) (Ioi x) x := by
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, diff_singleton_eq_self]
  have h_mono : MonotoneOn (slope f x) (Ioi x) := by
    refine monotoneOn_iff_forall_lt.mpr fun y (hy : x < y) z (hz : x < z) hz' ↦ ?_
    simp_rw [slope_def_field]
    exact hfc.secant_mono hx.le (hx.trans hy).le (hx.trans hz).le hy.ne' hz.ne' hz'.le
  exact MonotoneOn.tendsto_nhdsWithin_Ioi h_mono (bddBelow_slope_Ioi' hfc x hx)

lemma differentiableWithinAt_Ioi (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    DifferentiableWithinAt ℝ f (Ioi x) x :=
  (hfc.hasRightDerivAt x).differentiableWithinAt

lemma differentiableWithinAt_Ioi' (hfc : ConvexOn ℝ (Ici 0) f) (hx : 0 < x) :
    DifferentiableWithinAt ℝ f (Ioi x) x :=
  (hfc.hasRightDerivAt' hx).differentiableWithinAt

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

lemma rightDeriv_eq_sInf_slope' (hfc : ConvexOn ℝ (Ici 0) f) (hx : 0 < x) :
    rightDeriv f x = sInf (slope f x '' Ioi x) :=
  (hfc.hasRightDerivAt' hx).derivWithin (uniqueDiffWithinAt_Ioi x)

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

lemma rightDeriv_mono' (hfc : ConvexOn ℝ (Ici 0) f) : MonotoneOn (rightDeriv f) (Ioi 0) := by
  intro x (hx : 0 < x) y (hy : 0 < y) hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  rw [hfc.rightDeriv_eq_sInf_slope' hx, hfc.rightDeriv_eq_sInf_slope' hy]
  refine csInf_le_of_le (b := slope f x y) (bddBelow_slope_Ioi' hfc x hx)
    ⟨y, by simp [hxy]⟩ (le_csInf nonempty_of_nonempty_subtype ?_)
  rintro _ ⟨z, (yz : y < z), rfl⟩
  rw [slope_comm]
  exact slope_mono hfc hy.le ⟨hx.le, hxy.ne⟩ ⟨hy.le.trans yz.le, yz.ne'⟩ (hxy.trans yz).le

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

lemma rightDerivStieltjes_eq_rightDeriv (hf : ConvexOn ℝ univ f) :
    rightDerivStieltjes hf = rightDeriv f := rfl

lemma rightDerivStieltjes_const (c : ℝ) : rightDerivStieltjes (convexOn_const c convex_univ) = 0 := by
  ext x
  simp_rw [rightDerivStieltjes_eq_rightDeriv, rightDeriv_const]
  rfl

lemma rightDerivStieltjes_linear (a : ℝ) :
    rightDerivStieltjes (ConvexOn.const_mul_id a) = StieltjesFunction.const a := by
  ext x
  simp_rw [rightDerivStieltjes_eq_rightDeriv, rightDeriv_const_mul a, rightDeriv_id', mul_one]
  rfl

lemma rightDerivStieltjes_add {f g : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (hg : ConvexOn ℝ univ g) :
    rightDerivStieltjes (hf.add hg) = rightDerivStieltjes hf + rightDerivStieltjes hg := by
  ext x
  simp_rw [StieltjesFunction.add_apply, rightDerivStieltjes_eq_rightDeriv, rightDeriv_add_apply
    (hf.differentiableWithinAt_Ioi x) (hg.differentiableWithinAt_Ioi x)]

lemma rightDerivStieltjes_add_const (hf : ConvexOn ℝ univ f) (c : ℝ) :
    rightDerivStieltjes (hf.add (convexOn_const c convex_univ)) = rightDerivStieltjes hf := by
  rw [rightDerivStieltjes_add hf (convexOn_const c convex_univ), rightDerivStieltjes_const,
    add_zero]

end ConvexOn

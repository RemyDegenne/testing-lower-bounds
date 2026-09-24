/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Measure.Stieltjes


/-! # Left and right derivatives of convex functions

Properties of `leftDeriv` and `rightDeriv` of convex functions on `ℝ`, and of the Stieltjes
function `rightDerivStieltjes` associated to the right derivative.
-/

@[expose] public section

open Set Filter Topology

open scoped ENNReal NNReal

variable {f : ℝ → ℝ} {x : ℝ}

namespace ConvexOn

lemma comp_neg {𝕜 F β : Type*} [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup F]
    [AddCommMonoid β] [PartialOrder β]
    [Module 𝕜 F] [SMul 𝕜 β] {f : F → β} {s : Set F}
    (hf : ConvexOn 𝕜 s f) :
    ConvexOn 𝕜 (-s) (fun x ↦ f (-x)) := by
  refine ⟨hf.1.neg, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simp_rw [neg_add_rev, ← smul_neg, add_comm]
  exact hf.2 hx hy ha hb hab

--this can be stated in much greater generality
lemma const_mul_id (c : ℝ) : ConvexOn ℝ .univ (fun (x : ℝ) ↦ c * x) := by
  refine ⟨convex_univ, fun _ _ _ _ _ _ _ _ _ ↦ Eq.le ?_⟩
  simp only [smul_eq_mul]
  ring

end ConvexOn


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
  rw [rightDeriv_def, leftDeriv_def, derivWithin_comp_neg, neg_neg, neg_neg, neg_Iio, neg_neg]

lemma rightDeriv_eq_leftDeriv (f : ℝ → ℝ) :
    rightDeriv f = fun x ↦ - leftDeriv (fun y ↦ f (-y)) (-x) := by
  ext x
  simp [rightDeriv_eq_leftDeriv_apply]

lemma leftDeriv_eq_rightDeriv_apply (f : ℝ → ℝ) (x : ℝ) :
    leftDeriv f x = - rightDeriv (fun y ↦ f (-y)) (-x) := by
  simp [rightDeriv_eq_leftDeriv_apply]

lemma leftDeriv_eq_rightDeriv (f : ℝ → ℝ) :
    leftDeriv f = fun x ↦ - rightDeriv (fun y ↦ f (-y)) (-x) := by
  ext x
  simp [leftDeriv_eq_rightDeriv_apply]

lemma Filter.EventuallyEq.rightDeriv_eq_nhds {x : ℝ} {g : ℝ → ℝ} (h : f =ᶠ[𝓝 x] g) :
    rightDeriv f x = rightDeriv g x := h.derivWithin_eq_of_nhds

lemma rightDeriv_congr_atTop {g : ℝ → ℝ} (h : f =ᶠ[atTop] g) :
    rightDeriv f =ᶠ[atTop] rightDeriv g := by
  have h' : ∀ᶠ x in atTop, f =ᶠ[𝓝 x] g := by
    -- todo: replace by clean filter proof?
    simp only [Filter.EventuallyEq, eventually_atTop] at h ⊢
    obtain ⟨a, ha⟩ := h
    refine ⟨a + 1, fun b hab ↦ ?_⟩
    have h_ge : ∀ᶠ x in 𝓝 b, a ≤ x := eventually_ge_nhds ((lt_add_one _).trans_le hab)
    filter_upwards [h_ge] using ha
  filter_upwards [h'] with a ha using ha.rightDeriv_eq_nhds

lemma rightDeriv_congr_nhdsGE {g : ℝ → ℝ} (h : f =ᶠ[𝓝[≥] x] g) :
    rightDeriv f x = rightDeriv g x :=
  Filter.EventuallyEq.derivWithin_eq (h.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self))
    (h.eq_of_nhdsWithin Set.self_mem_Ici)

lemma rightDeriv_of_hasDerivAt {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (h : HasDerivAt f f' x) :
    rightDeriv f x = f' := by
  rw [rightDeriv_def, h.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)]

lemma leftDeriv_of_hasDerivAt {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (h : HasDerivAt f f' x) :
    leftDeriv f x = f' := by
  rw [leftDeriv_def, h.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)]

@[simp]
lemma rightDeriv_zero : rightDeriv 0 = 0 := by
  ext x
  simp only [rightDeriv, Pi.zero_apply]
  simp

@[simp]
lemma rightDeriv_const (c : ℝ) : rightDeriv (fun _ ↦ c) = 0 := by
  ext x
  rw [rightDeriv_def, Pi.zero_apply]
  simp

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
  · simp_rw [rightDeriv_def, derivWithin_const_mul _ hfx]
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
  simp_rw [rightDeriv_def, ← derivWithin_add hf hg]

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
  simp_rw [leftDeriv_def, ← derivWithin_add hf hg]

lemma leftDeriv_add_apply' {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableWithinAt ℝ f (Iio x) x)
    (hg : DifferentiableWithinAt ℝ g (Iio x) x) :
    leftDeriv (fun x ↦ f x + g x) x = leftDeriv f x + leftDeriv g x :=
  leftDeriv_add_apply hf hg

lemma leftDeriv_add {f g : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Iio x) x)
    (hg : ∀ x, DifferentiableWithinAt ℝ g (Iio x) x) :
    leftDeriv (f + g) = fun x ↦ leftDeriv f x + leftDeriv g x := by
  ext x; exact leftDeriv_add_apply (hf x) (hg x)

lemma leftDeriv_add' {f g : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Iio x) x)
    (hg : ∀ x, DifferentiableWithinAt ℝ g (Iio x) x) :
    leftDeriv (fun x ↦ f x + g x) = fun x ↦ leftDeriv f x + leftDeriv g x := by
  simp_rw [← Pi.add_apply f g, leftDeriv_add hf hg]

lemma rightDeriv_add_const_apply {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableWithinAt ℝ f (Ioi x) x)
    (c : ℝ) :
    rightDeriv (fun x ↦ f x + c) x = rightDeriv f x := by
  rw [rightDeriv_add_apply' hf (differentiableWithinAt_const c), rightDeriv_const,
    Pi.zero_apply, add_zero]

lemma rightDeriv_add_const {f : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Ioi x) x) (c : ℝ) :
    rightDeriv (fun x ↦ f x + c) = rightDeriv f := by
  ext x; exact rightDeriv_add_const_apply (hf x) c

lemma leftDeriv_add_const_apply {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableWithinAt ℝ f (Iio x) x)
    (c : ℝ) :
    leftDeriv (fun x ↦ f x + c) x = leftDeriv f x := by
  rw [leftDeriv_add_apply' hf (differentiableWithinAt_const c), leftDeriv_const,
    Pi.zero_apply, add_zero]

lemma leftDeriv_add_const {f : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Iio x) x) (c : ℝ) :
    leftDeriv (fun x ↦ f x + c) = leftDeriv f := by
  ext x; exact leftDeriv_add_const_apply (hf x) c

lemma rightDeriv_add_linear_apply {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableWithinAt ℝ f (Ioi x) x)
    (a : ℝ) :
    rightDeriv (fun x ↦ f x + a * x) x = rightDeriv f x + a := by
  rw [rightDeriv_add_apply' hf (by fun_prop), rightDeriv_const_mul, rightDeriv_id']
  simp

lemma rightDeriv_add_linear {f : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Ioi x) x) (a : ℝ) :
    rightDeriv (fun x ↦ f x + a * x) = rightDeriv f + fun _ ↦ a := by
  ext x; exact rightDeriv_add_linear_apply (hf x) a

lemma leftDeriv_add_linear_apply {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableWithinAt ℝ f (Iio x) x)
    (a : ℝ) :
    leftDeriv (fun x ↦ f x + a * x) x = leftDeriv f x + a := by
  rw [leftDeriv_add_apply' hf (by fun_prop), leftDeriv_const_mul, leftDeriv_id']
  simp

lemma leftDeriv_add_linear {f : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Iio x) x) (a : ℝ) :
    leftDeriv (fun x ↦ f x + a * x) = leftDeriv f + fun _ ↦ a := by
  ext x; exact leftDeriv_add_linear_apply (hf x) a


namespace ConvexOn

section GeneralSet

variable {s : Set ℝ} {x : ℝ}

lemma rightDeriv_right_continuous_of_mem_interior (hfc : ConvexOn ℝ s f)
    {w : ℝ} (hw : w ∈ interior s) :
    ContinuousWithinAt (rightDeriv f) (Ici w) w := by
  have h_mono : MonotoneOn (rightDeriv f) (interior s) := hfc.monotoneOn_rightDeriv
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
  obtain ⟨a, b, hwab, habs⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (mem_interior_iff_mem_nhds.mp hw)
  have h_int : Ioo a b ⊆ interior s := isOpen_Ioo.subset_interior_iff.mpr habs
  have h_mem : ∀ z ∈ Ioo w b, z ∈ interior s := fun z hz ↦ h_int ⟨hwab.1.trans hz.1, hz.2⟩
  have h_bdd : BddBelow (rightDeriv f '' Ioo w b) := by
    refine ⟨rightDeriv f w, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact h_mono hw (h_mem z hz) hz.1.le
  have h_lim := (h_mono.mono h_mem).tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hwab.2) h_bdd
  convert h_lim
  refine le_antisymm (le_csInf ((nonempty_Ioo.mpr hwab.2).image _) ?_) ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact h_mono hw (h_mem z hz) hz.1.le
  · rw [rightDeriv_def, hfc.rightDeriv_eq_sInf_slope_of_mem_interior hw]
    refine le_csInf ?_ ?_
    · obtain ⟨z, hwz, hzb⟩ := exists_between hwab.2
      exact ⟨_, z, ⟨habs ⟨hwab.1.trans hwz, hzb⟩, hwz⟩, rfl⟩
    rintro _ ⟨y, ⟨hys, hwy⟩, rfl⟩
    have h_cont : ContinuousWithinAt f (Ioi w) w :=
      (hfc.differentiableWithinAt_Ioi_of_mem_interior hw).continuousWithinAt
    have slope_lim : Tendsto (slope f y) (𝓝[>] w) (𝓝 (slope f y w)) :=
      ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀ (sub_ne_zero.2 hwy.ne)).smul
        (h_cont.sub continuousWithinAt_const) |>.tendsto
    rw [slope_comm] at slope_lim
    refine le_of_tendsto_of_tendsto tendsto_const_nhds slope_lim ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min hwy hwab.2)] with z hz
    have hz' : z ∈ Ioo w b := ⟨hz.1, hz.2.trans_le (min_le_right _ _)⟩
    calc sInf (rightDeriv f '' Ioo w b) ≤ rightDeriv f z := csInf_le h_bdd ⟨z, hz', rfl⟩
    _ ≤ slope f z y := hfc.rightDeriv_le_slope_of_mem_interior (h_mem z hz') hys
        (hz.2.trans_le (min_le_left _ _))
    _ = slope f y z := slope_comm _ _ _

lemma leftDeriv_left_continuous_of_mem_interior (hfc : ConvexOn ℝ s f)
    {w : ℝ} (hw : w ∈ interior s) :
    ContinuousWithinAt (leftDeriv f) (Iic w) w := by
  have h_map : MapsTo Neg.neg (Iic w) (Ici (-w)) := fun _ (h : _ ≤ w) ↦ (neg_le_neg_iff.mpr h)
  have hw' : -w ∈ interior (-s) :=
    isOpen_interior.neg.subset_interior_iff.mpr (neg_subset_neg.mpr interior_subset)
      (neg_mem_neg.mpr hw)
  rw [leftDeriv_eq_rightDeriv]
  exact (hfc.comp_neg.rightDeriv_right_continuous_of_mem_interior hw').comp
    continuousWithinAt_neg h_map |>.neg

end GeneralSet

section Univ

lemma hasRightDerivAt (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    HasDerivWithinAt f (sInf (slope f x '' Ioi x)) (Ioi x) x := by
  have h := hfc.hasDerivWithinAt_sInf_slope_of_mem_interior (x := x) (by simp)
  rwa [show {y ∈ (univ : Set ℝ) | x < y} = Ioi x by ext; simp] at h

lemma hasRightDerivAt' (hfc : ConvexOn ℝ (Ici 0) f) (hx : 0 < x) :
    HasDerivWithinAt f (sInf (slope f x '' Ioi x)) (Ioi x) x := by
  have h := hfc.hasDerivWithinAt_sInf_slope_of_mem_interior (x := x) (by simpa using hx)
  rwa [show {y ∈ Ici (0 : ℝ) | x < y} = Ioi x by
    ext z
    simp only [mem_ofPred_eq, mem_Ici, mem_Ioi]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨(hx.trans h).le, h⟩⟩]
    at h

lemma differentiableWithinAt_Ioi (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    DifferentiableWithinAt ℝ f (Ioi x) x :=
  hfc.differentiableWithinAt_Ioi_of_mem_interior (by simp)

lemma differentiableWithinAt_Ioi' (hfc : ConvexOn ℝ (Ici 0) f) (hx : 0 < x) :
    DifferentiableWithinAt ℝ f (Ioi x) x :=
  hfc.differentiableWithinAt_Ioi_of_mem_interior (by simpa using hx)

lemma hadDerivWithinAt_rightDeriv (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    HasDerivWithinAt f (rightDeriv f x) (Ioi x) x :=
  hfc.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)

lemma hasLeftDerivAt (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    HasDerivWithinAt f (sSup (slope f x '' Iio x)) (Iio x) x := by
  have h := hfc.hasDerivWithinAt_sSup_slope_of_mem_interior (x := x) (by simp)
  rwa [show {y ∈ (univ : Set ℝ) | y < x} = Iio x by ext; simp] at h

lemma differentiableWithinAt_Iio (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    DifferentiableWithinAt ℝ f (Iio x) x :=
  hfc.differentiableWithinAt_Iio_of_mem_interior (by simp)

lemma hadDerivWithinAt_leftDeriv (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    HasDerivWithinAt f (leftDeriv f x) (Iio x) x :=
  hfc.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)

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
  have h : MonotoneOn (rightDeriv f) (interior univ) := hfc.monotoneOn_rightDeriv
  simpa using h

lemma rightDeriv_mono' (hfc : ConvexOn ℝ (Ici 0) f) : MonotoneOn (rightDeriv f) (Ioi 0) := by
  have h := hfc.monotoneOn_rightDeriv
  rwa [interior_Ici] at h

lemma leftDeriv_mono (hfc : ConvexOn ℝ univ f) : Monotone (leftDeriv f) := by
  have h : MonotoneOn (leftDeriv f) (interior univ) := hfc.monotoneOn_leftDeriv
  simpa using h

lemma leftDeriv_le_rightDeriv (hfc : ConvexOn ℝ univ f) : leftDeriv f ≤ rightDeriv f :=
  fun _ ↦ hfc.leftDeriv_le_rightDeriv_of_mem_interior (by simp)

lemma rightDeriv_right_continuous (hfc : ConvexOn ℝ univ f) (w : ℝ) :
    ContinuousWithinAt (rightDeriv f) (Ici w) w :=
  hfc.rightDeriv_right_continuous_of_mem_interior (by simp)

lemma leftDeriv_left_continuous (hfc : ConvexOn ℝ univ f) (w : ℝ) :
    ContinuousWithinAt (leftDeriv f) (Iic w) w :=
  hfc.leftDeriv_left_continuous_of_mem_interior (by simp)

end Univ

/-- The right derivative of a convex real function is a Stieltjes function. -/
noncomputable
def rightDerivStieltjes {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    StieltjesFunction ℝ where
  toFun := rightDeriv f
  mono' _ _ := fun h ↦ hf.rightDeriv_mono h
  right_continuous' _ := hf.rightDeriv_right_continuous _

lemma rightDerivStieltjes_eq_rightDeriv (hf : ConvexOn ℝ univ f) :
    rightDerivStieltjes hf = rightDeriv f := rfl

lemma rightDerivStieltjes_const (c : ℝ) :
    rightDerivStieltjes (convexOn_const c convex_univ) = 0 := by
  ext x
  simp_rw [rightDerivStieltjes_eq_rightDeriv, rightDeriv_const]
  rfl

lemma rightDerivStieltjes_linear (a : ℝ) :
    rightDerivStieltjes (ConvexOn.const_mul_id a) = StieltjesFunction.const ℝ a := by
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

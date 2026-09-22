/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Measure.Stieltjes


open Set Filter Topology

open scoped ENNReal NNReal

variable {f : ℝ → ℝ} {x : ℝ}

namespace ConvexOn

lemma comp_neg {𝕜 F β : Type*} [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup F]
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    [Module 𝕜 F] [SMul 𝕜 β] {f : F → β} {s : Set F}
    (hf : ConvexOn 𝕜 s f) :
    ConvexOn 𝕜 (-s) (fun x ↦ f (-x)) := by
  refine ⟨hf.1.neg, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simp_rw [neg_add_rev, ← smul_neg, add_comm]
  exact hf.2 hx hy ha hb hab

lemma comp_neg_iff {𝕜 F β : Type*} [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup F]
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    [Module 𝕜 F] [SMul 𝕜 β] {f : F → β} {s : Set F}  :
    ConvexOn 𝕜 (-s) (fun x ↦ f (-x)) ↔ ConvexOn 𝕜 s f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ConvexOn.comp_neg h⟩
  rw [← neg_neg s, ← Function.comp_id f, ← neg_comp_neg, ← Function.comp_assoc]
  exact h.comp_neg

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
  change rightDeriv f x = -leftDeriv (f ∘ Neg.neg) (-x)
  have h_map : MapsTo Neg.neg (Iio (-x)) (Ioi x) := fun _ (h : _ < -x) ↦ lt_neg_of_lt_neg h
  have h_map' : MapsTo Neg.neg (Ioi x) (Iio (-x)) := fun _ (h : x < _) ↦ neg_lt_neg h
  by_cases hf_diff : DifferentiableWithinAt ℝ f (Ioi x) x
  swap
  · rw [rightDeriv_def, leftDeriv_def, derivWithin_zero_of_not_differentiableWithinAt hf_diff,
      derivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    contrapose! hf_diff
    have h := DifferentiableWithinAt.comp x hf_diff ((differentiable_neg _).differentiableWithinAt)
      h_map'
    simpa [Function.comp_def] using h
  simp_rw [leftDeriv]
  rw [derivWithin_comp _ ((neg_neg x).symm ▸ hf_diff) (differentiable_neg _).differentiableWithinAt
    h_map, neg_neg, ← rightDeriv_def, derivWithin_neg]
  swap; · exact uniqueDiffWithinAt_Iio _
  simp only [mul_neg, mul_one, neg_neg]

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

lemma Filter.EventuallyEq.derivWithin_eq_nhds {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f₁ f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}
    (h : f₁ =ᶠ[𝓝 x] f) :
    derivWithin f₁ s x = derivWithin f s x := by
  simp_rw [derivWithin]
  rw [fderivWithin_eq_of_nhds h]

lemma Filter.EventuallyEq.rightDeriv_eq_nhds {x : ℝ} {g : ℝ → ℝ} (h : f =ᶠ[𝓝 x] g) :
    rightDeriv f x = rightDeriv g x := h.derivWithin_eq_nhds

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

section Slope

variable {s : Set ℝ}

lemma bddBelow_slope_Ioi (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    BddBelow (slope f x '' Ioi x) := by
  refine bddBelow_iff_subset_Ici.mpr ⟨slope f x (x - 1), fun y ⟨z, (hz : x < z), hz'⟩ ↦ ?_⟩
  simp_rw [mem_Ici, ← hz']
  exact slope_mono hfc trivial (by simp) ⟨trivial, hz.ne'⟩ (by linarith)

lemma bddBelow_slope_Ioi' (hfc : ConvexOn ℝ (Ici 0) f) (x : ℝ) (hx : 0 < x) :
    BddBelow (slope f x '' Ioi x) := by
  refine bddBelow_iff_subset_Ici.mpr ⟨slope f x 0, fun y ⟨z, (hz : x < z), hz'⟩ ↦ ?_⟩
  simp_rw [mem_Ici, ← hz']
  exact slope_mono hfc hx.le (by simp [hx.ne]) ⟨(hx.trans hz).le, hz.ne'⟩ (by linarith)

lemma bddAbove_slope_Iio (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    BddAbove (slope f x '' Iio x) := by
  refine bddAbove_iff_subset_Iic.mpr ⟨slope f x (x + 1), fun y ⟨z, (hz : z < x), hz'⟩ ↦ ?_⟩
  simp_rw [mem_Iic, ← hz']
  exact slope_mono hfc (mem_univ x) ⟨trivial, hz.ne⟩ (by simp) (by linarith)

lemma bddBelow_slope_Ioi_of_mem_interior (hfc : ConvexOn ℝ s f) {x : ℝ} (hxs : x ∈ interior s) :
    BddBelow (slope f x '' {y ∈ s | x < y}) := by
  obtain ⟨y, hys, hyx⟩ : ∃ y ∈ s, y < x := by
    rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs
    obtain ⟨a, b, hxab, habs⟩ := hxs
    rw [mem_Ioo] at hxab
    obtain ⟨a', haa', ha'x⟩ := exists_between hxab.1
    exact ⟨a', habs ⟨haa', ha'x.trans hxab.2⟩, ha'x⟩
  refine bddBelow_iff_subset_Ici.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ ↦ ?_⟩
  simp_rw [mem_Ici, ← hz']
  refine slope_mono hfc (interior_subset hxs) ?_ ?_ (hyx.trans hz.2).le
  · simp [hys, hyx.ne]
  · simp [hz.2.ne', hz.1]

lemma bddAbove_slope_Iio_of_mem_interior (hfc : ConvexOn ℝ s f) {x : ℝ} (hxs : x ∈ interior s) :
    BddAbove (slope f x '' {y ∈ s | y < x}) := by
  obtain ⟨y, hys, hyx⟩ : ∃ y ∈ s, x < y := by
    rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs
    obtain ⟨a, b, hxab, habs⟩ := hxs
    rw [mem_Ioo] at hxab
    obtain ⟨b', hxb', hb'b⟩ := exists_between hxab.2
    exact ⟨b', habs ⟨hxab.1.trans hxb', hb'b⟩, hxb'⟩
  refine bddAbove_iff_subset_Iic.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ ↦ ?_⟩
  simp_rw [mem_Iic, ← hz']
  refine slope_mono hfc (interior_subset hxs) ?_ ?_ (hz.2.trans hyx).le
  · simp [hz.2.ne, hz.1]
  · simp [hys, hyx.ne']

end Slope

section GeneralSet

variable {s : Set ℝ} {x : ℝ}

lemma hasRightDerivAt_of_mem_interior (hfc : ConvexOn ℝ s f) (hxs : x ∈ interior s) :
    HasDerivWithinAt f (sInf (slope f x '' {y ∈ s | x < y})) (Ioi x) x := by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, sdiff_singleton_eq_self]
  have h_mono : MonotoneOn (slope f x) {y ∈ s | x < y} := monotoneOn_slope_gt hfc (habs hxab)
  have h_bddBelow : BddBelow (slope f x '' Ioo x b) := by
    refine (bddBelow_slope_Ioi_of_mem_interior hfc hxs).mono ?_
    refine image_subset_iff.mpr ?_
    grind
  have h_Ioo : Tendsto (slope f x) (𝓝[>] x) (𝓝 (sInf (slope f x '' Ioo x b))) := by
    refine MonotoneOn.tendsto_nhdsWithin_Ioo_right ?_ ?_ h_bddBelow
    · simpa using hxab.2
    · exact h_mono.mono fun z hz ↦ ⟨habs ⟨hxab.1.trans hz.1, hz.2⟩, hz.1⟩
  suffices sInf (slope f x '' Ioo x b) = sInf (slope f x '' {y ∈ s | x < y}) by rwa [← this]
  apply le_antisymm
  · refine le_csInf ?_ fun z hz ↦ ?_
    · simp only [image_nonempty]
      obtain ⟨z, hxz, hzb⟩ := exists_between hxab.2
      exact ⟨z, habs ⟨hxab.1.trans hxz, hzb⟩, hxz⟩
    · simp only [mem_image, mem_ofPred_eq] at hz
      obtain ⟨y, ⟨hys, hxy⟩, rfl⟩ := hz
      obtain ⟨z, hxz, hzy⟩ := exists_between (lt_min hxab.2 hxy)
      refine csInf_le_of_le (b := slope f x z) h_bddBelow ?_ ?_
      · exact ⟨z, ⟨hxz, hzy.trans_le (min_le_left _ _)⟩, rfl⟩
      · refine monotoneOn_slope_gt hfc (interior_subset hxs) ?_ ⟨hys, hxy⟩ (hzy.le.trans (min_le_right _ _))
        exact ⟨habs ⟨hxab.1.trans hxz, hzy.trans_le (min_le_left _ _)⟩, hxz⟩
  · refine csInf_le_csInf (bddBelow_slope_Ioi_of_mem_interior hfc hxs) ?_ ?_
    · simpa using hxab.2
    · refine image_subset_iff.mpr ?_
      grind

lemma hasLeftDerivAt_of_mem_interior (hfc : ConvexOn ℝ s f) (hxs : x ∈ interior s) :
    HasDerivWithinAt f (sSup (slope f x '' {y ∈ s | y < x})) (Iio x) x := by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Iio, lt_self_iff_false, not_false_eq_true, sdiff_singleton_eq_self]
  have h_mono : MonotoneOn (slope f x) {y ∈ s | y < x} := monotoneOn_slope_lt hfc (interior_subset hxs)
  have h_bddAbove : BddAbove (slope f x '' Ioo a x) := by
    refine (bddAbove_slope_Iio_of_mem_interior hfc hxs).mono ?_
    exact image_mono fun z hz ↦ ⟨habs ⟨hz.1, hz.2.trans hxab.2⟩, hz.2⟩
  have h_Ioo : Tendsto (slope f x) (𝓝[<] x) (𝓝 (sSup (slope f x '' Ioo a x))) := by
    refine MonotoneOn.tendsto_nhdsWithin_Ioo_left ?_ ?_ h_bddAbove
    · simpa using hxab.1
    · exact h_mono.mono fun z hz ↦ ⟨habs ⟨hz.1, hz.2.trans hxab.2⟩, hz.2⟩
  suffices sSup (slope f x '' Ioo a x) = sSup (slope f x '' {y ∈ s | y < x}) by rwa [← this]
  apply le_antisymm
  · refine csSup_le_csSup (bddAbove_slope_Iio_of_mem_interior hfc hxs) ?_ ?_
    · simpa using hxab.1
    · refine image_mono fun z hz ↦ ?_
      exact ⟨habs ⟨hz.1, hz.2.trans hxab.2⟩, hz.2⟩
  · refine csSup_le ?_ fun z hz ↦ ?_
    · simp only [image_nonempty]
      obtain ⟨z, haz, hzx⟩ := exists_between hxab.1
      exact ⟨z, habs ⟨haz, hzx.trans hxab.2⟩, hzx⟩
    · simp only [mem_image, mem_ofPred_eq] at hz
      obtain ⟨y, ⟨hys, hyx⟩, rfl⟩ := hz
      obtain ⟨z, hxz, hzy⟩ := exists_between (max_lt hxab.1 hyx)
      refine le_csSup_of_le (b := slope f x z) h_bddAbove ?_ ?_
      · exact ⟨z, ⟨(le_max_left _ _).trans_lt hxz, hzy⟩, rfl⟩
      · refine monotoneOn_slope_lt hfc (interior_subset hxs) ⟨hys, hyx⟩ ?_ ((le_max_right _ _).trans hxz.le)
        exact ⟨habs ⟨(le_max_left _ _).trans_lt hxz, hzy.trans hxab.2⟩, hzy⟩

lemma rightDeriv_monotoneOn (hfc : ConvexOn ℝ s f) : MonotoneOn (rightDeriv f) (interior s) := by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [rightDeriv_def, hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs,
    hfc.rightDeriv_eq_sInf_slope_of_mem_interior hys]
  refine csInf_le_of_le (b := slope f x y) (bddBelow_slope_Ioi_of_mem_interior hfc hxs)
    ⟨y, by simp only [mem_ofPred_eq, hxy, and_true]; exact interior_subset hys⟩
    (le_csInf ?_ ?_)
  · have hys' := hys
    rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hys'
    obtain ⟨a, b, hxab, habs⟩ := hys'
    rw [image_nonempty]
    obtain ⟨z, hxz, hzb⟩ := exists_between hxab.2
    exact ⟨z, habs ⟨hxab.1.trans hxz, hzb⟩, hxz⟩
  · rintro _ ⟨z, ⟨hzs, hyz : y < z⟩, rfl⟩
    rw [slope_comm]
    exact slope_mono hfc (interior_subset hys) ⟨interior_subset hxs, hxy.ne⟩ ⟨hzs, hyz.ne'⟩
      (hxy.trans hyz).le

lemma leftDeriv_monotoneOn (hfc : ConvexOn ℝ s f) : MonotoneOn (leftDeriv f) (interior s) := by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [leftDeriv_def, hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs,
    hfc.leftDeriv_eq_sSup_slope_of_mem_interior hys]
  refine le_csSup_of_le (b := slope f x y) (bddAbove_slope_Iio_of_mem_interior hfc hys)
    ⟨x, by simp only [slope_comm, mem_ofPred_eq, hxy, and_true]; exact interior_subset hxs⟩
    (csSup_le ?_ ?_)
  · have hxs' := hxs
    rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs'
    obtain ⟨a, b, hxab, habs⟩ := hxs'
    rw [image_nonempty]
    obtain ⟨z, hxz, hzb⟩ := exists_between hxab.1
    exact ⟨z, habs ⟨hxz, hzb.trans hxab.2⟩, hzb⟩
  · rintro _ ⟨z, ⟨hzs, hyz : z < x⟩, rfl⟩
    exact slope_mono hfc (interior_subset hxs) ⟨hzs, hyz.ne⟩ ⟨interior_subset hys, hxy.ne'⟩
      (hyz.trans hxy).le

lemma rightDeriv_right_continuous_of_mem_interior (hfc : ConvexOn ℝ s f)
    {w : ℝ} (hw : w ∈ interior s) :
    ContinuousWithinAt (rightDeriv f) (Ici w) w := by
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
  obtain ⟨a, b, hwab, habs⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (mem_interior_iff_mem_nhds.mp hw)
  have h_int : Ioo a b ⊆ interior s := isOpen_Ioo.subset_interior_iff.mpr habs
  have h_mem : ∀ z ∈ Ioo w b, z ∈ interior s := fun z hz ↦ h_int ⟨hwab.1.trans hz.1, hz.2⟩
  have h_bdd : BddBelow (rightDeriv f '' Ioo w b) := by
    refine ⟨rightDeriv f w, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hfc.rightDeriv_monotoneOn hw (h_mem z hz) hz.1.le
  have h_lim := (hfc.rightDeriv_monotoneOn.mono h_mem).tendsto_nhdsWithin_Ioo_right
    (nonempty_Ioo.mpr hwab.2) h_bdd
  convert h_lim
  refine le_antisymm (le_csInf ((nonempty_Ioo.mpr hwab.2).image _) ?_) ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact hfc.rightDeriv_monotoneOn hw (h_mem z hz) hz.1.le
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

lemma leftDeriv_left_continuous_of_mem_interior (hfc : ConvexOn ℝ univ f)
    {w : ℝ} (hw : w ∈ interior s) :
    ContinuousWithinAt (leftDeriv f) (Iic w) w := by
  sorry
  -- have h_map : MapsTo Neg.neg (Iic w) (Ici (-w)) := fun _ (h : _ ≤ w) ↦ (neg_le_neg_iff.mpr h)
  -- rw [leftDeriv_eq_rightDeriv]
  -- exact (hfc.comp_neg.rightDeriv_right_continuous _).comp continuousWithinAt_neg h_map |>.neg

end GeneralSet

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
  convert hasRightDerivAt_of_mem_interior hfc (x := x) (by simp)
  simp only [mem_univ, true_and]
  rfl

lemma hasRightDerivAt' (hfc : ConvexOn ℝ (Ici 0) f) (hx : 0 < x) :
    HasDerivWithinAt f (sInf (slope f x '' Ioi x)) (Ioi x) x := by
  convert hasRightDerivAt_of_mem_interior hfc (x := x) ?_
  · ext z
    simp only [mem_Ioi, mem_Ici, mem_ofPred_eq, iff_and_self]
    exact fun hxz ↦ (hx.trans hxz).le
  · simpa using hx

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
  simp only [mem_Iio, lt_self_iff_false, not_false_eq_true, sdiff_singleton_eq_self]
  have h_mono : MonotoneOn (slope f x) (Iio x) := by
    refine monotoneOn_iff_forall_lt.mpr fun y (hy : y < x) z (hz : z < x) hz' ↦ ?_
    simp_rw [slope_def_field]
    exact hfc.secant_mono trivial trivial trivial hy.ne hz.ne hz'.le
  exact MonotoneOn.tendsto_nhdsLT h_mono (bddAbove_slope_Iio hfc x)

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
    ⟨y, by simp [hxy]⟩ (le_csInf Set.Nonempty.of_subtype ?_)
  rintro _ ⟨z, (yz : y < z), rfl⟩
  rw [slope_comm]
  exact slope_mono hfc trivial ⟨trivial, hxy.ne⟩ ⟨trivial, yz.ne'⟩ (hxy.trans yz).le

lemma rightDeriv_mono' (hfc : ConvexOn ℝ (Ici 0) f) : MonotoneOn (rightDeriv f) (Ioi 0) := by
  intro x (hx : 0 < x) y (hy : 0 < y) hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  rw [hfc.rightDeriv_eq_sInf_slope' hx, hfc.rightDeriv_eq_sInf_slope' hy]
  refine csInf_le_of_le (b := slope f x y) (bddBelow_slope_Ioi' hfc x hx)
    ⟨y, by simp [hxy]⟩ (le_csInf Set.Nonempty.of_subtype ?_)
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
  refine csSup_le Set.Nonempty.of_subtype ?_
  rintro _ ⟨z, (zx : z < x), rfl⟩
  refine le_csInf Set.Nonempty.of_subtype ?_
  rintro _ ⟨y, (xy : x < y), rfl⟩
  exact slope_mono hfc trivial ⟨trivial, zx.ne⟩ ⟨trivial, xy.ne'⟩ (zx.trans xy).le

lemma rightDeriv_right_continuous (hfc : ConvexOn ℝ univ f) (w : ℝ) :
    ContinuousWithinAt (rightDeriv f) (Ici w) w := by
  simp_rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
  have h_lim := MonotoneOn.tendsto_nhdsGT (hfc.rightDeriv_mono.monotoneOn (Ioi w))
    (Monotone.map_bddBelow hfc.rightDeriv_mono bddBelow_Ioi)
  set l := sInf (rightDeriv f '' Ioi w)
  convert h_lim
  apply le_antisymm
  · exact ge_of_tendsto h_lim <| eventually_nhdsWithin_of_forall
      fun y (hy : w < y) ↦ hfc.rightDeriv_mono hy.le
  · rw [hfc.rightDeriv_eq_sInf_slope]
    refine le_csInf Set.Nonempty.of_subtype ?_ --is there any way to avoid the rintro here? if I just use fun inside the refine it does not work, it seems that the rfl inside the pattern is not supported by the refine tactic
    rintro _ ⟨y, (wy : w < y), rfl⟩
    have slope_lim : Tendsto (slope f y) (𝓝[>] w) (𝓝 (slope f y w)) := by
      have hf_cont : ContinuousWithinAt f (Ioi w) w := -- I would like to replace this with a lemma that derives the continuity from the convexity, it seems that this result is still not in mathlib, see https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Continuity.20.20of.20convex.20functions, they are in the process of proving it in the LeanCamCombi project
        DifferentiableWithinAt.continuousWithinAt (hfc.differentiableWithinAt_Ioi w)
      exact ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀ (sub_ne_zero.2 wy.ne)).smul
        (hf_cont.sub continuousWithinAt_const) |>.tendsto
    rw [slope_comm] at slope_lim
    refine le_of_tendsto_of_tendsto h_lim slope_lim ?_
    rw [← nhdsWithin_Ioo_eq_nhdsGT wy]
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
    StieltjesFunction ℝ where
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

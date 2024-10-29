/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import TestingLowerBounds.ForMathlib.EReal

/-!
# Stieltjes measures on the real line

Consider a function `f : ℝ → EReal` which is monotone and right-continuous. Then one can define a
corresponding measure, giving mass `f b - f a` to the interval `(a, b]`.

## Main definitions

* `ERealStieltjes` is a structure containing a function from `ℝ → EReal`, together with the
assertions that it is monotone and right-continuous. To `f : ERealStieltjes`, one associates
a Borel measure `f.measure`.
* `f.measure_Ioc` asserts that `f.measure (Ioc a b) = ofReal (f b - f a)`
* `f.measure_Ioo` asserts that `f.measure (Ioo a b) = ofReal (leftLim f b - f a)`.
* `f.measure_Icc` and `f.measure_Ico` are analogous.
-/

noncomputable section

open Set Filter Function ENNReal NNReal Topology MeasureTheory

open ENNReal (ofReal)

section EReal

@[simp]
lemma EReal.toENNReal_one : (1 : EReal).toENNReal = 1 := by
  rw [EReal.toENNReal, if_neg (ne_of_beq_false rfl)]
  simp

lemma EReal.add_eq_top_iff {x y : EReal} : x + y = ⊤ ↔ x = ⊤ ∧ y ≠ ⊥ ∨ x ≠ ⊥ ∧ y = ⊤ := by
  induction x <;> induction y
  · simp
  · simp
  · simp
  · simp
  · simp only [EReal.coe_ne_top, ne_eq, EReal.coe_ne_bot, not_false_eq_true, and_true, and_false,
      or_self, iff_false]
    norm_cast
    exact EReal.coe_ne_top _
  · simp
  · simp
  · simp
  · simp

lemma EReal.sub_add_sub_cancel (b a : EReal) (c : ℝ) :
    b - c + (c - a) = b - a := by
  induction a <;> induction b
  · simp
  · simp only [coe_sub_bot]
    rw [← coe_sub, coe_add_top]
  · simp
  · simp
  · norm_cast
    ring
  · simp only [top_sub_coe]
    rw [← coe_sub, top_add_coe]
  · simp
  · simp
  · simp

lemma EReal.toENNReal_sub_le_add (b a c : EReal) :
    (b - a).toENNReal ≤ (b - c).toENNReal + (c - a).toENNReal := by
  by_cases hc_top : c = ⊤
  · simp only [hc_top, EReal.sub_top, ne_eq, bot_ne_top, not_false_eq_true,
      EReal.toENNReal_of_ne_top, EReal.toReal_bot, ofReal_zero, zero_add]
    by_cases ha : a = ⊤
    · simp [ha]
    · simp [EReal.top_sub_of_ne_top ha]
  by_cases hc_bot : c = ⊥
  · simp [hc_bot, sub_eq_add_neg]
    by_cases hb_bot : b = ⊥
    · simp [hb_bot]
    · simp [EReal.add_top_of_ne_bot hb_bot]
  refine (EReal.toENNReal_le_toENNReal ?_).trans EReal.toENNReal_add_le
  lift c to ℝ using ⟨hc_top, hc_bot⟩ with c
  rw [EReal.sub_add_sub_cancel]

lemma EReal.toENNReal_sub_eq_add {b a c : EReal} (hac : a ≤ c) (hcb : c ≤ b) :
    (b - a).toENNReal = (b - c).toENNReal + (c - a).toENNReal := by
  induction c
  · have ha : a = ⊥ := eq_bot_iff.mpr hac
    simp [ha]
  · rw [← EReal.toENNReal_add, EReal.sub_add_sub_cancel]
    · rwa [EReal.sub_nonneg (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    · by_cases ha : a = ⊥
      · simp [ha]
      rwa [EReal.sub_nonneg _ ha]
      exact (hac.trans_lt (EReal.coe_lt_top _)).ne
  · have hb : b = ⊤ := eq_top_iff.mpr hcb
    simp [hb]

lemma EReal.toENNReal_eq_toENNReal_iff {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x.toENNReal = y.toENNReal ↔ x = y := by
  induction x <;> induction y
  · simp
  · simp at hx
  · simp
  · simp at hy
  · simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
      EReal.toReal_coe, EReal.coe_eq_coe_iff]
    rw [ENNReal.ofReal_eq_ofReal_iff]
    · exact mod_cast hx
    · exact mod_cast hy
  · simp
  · simp
  · simp
  · simp

lemma EReal.continuousAt_sub {p : EReal × EReal} (h : p.1 ≠ ⊤ ∨ p.2 ≠ ⊤) (h' : p.1 ≠ ⊥ ∨ p.2 ≠ ⊥) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 - p.2) p := by
  simp_rw [sub_eq_add_neg]
  change ContinuousAt ((fun p : EReal × EReal => p.1 + p.2) ∘ (fun p ↦ (p.1, -p.2))) p
  refine ContinuousAt.comp ?_ ?_
  · refine EReal.continuousAt_add ?_ ?_
    · simp [h]
    · simp [h']
  · fun_prop

lemma EReal.continuousAt_const_sub {c x : EReal} (h' : x ≠ ⊤ ∨ c ≠ ⊤) :
    ContinuousAt (fun x : EReal ↦ c - x) x := by
  by_cases hc_top : c = ⊥
  · simp [hc_top]
    exact continuous_const.continuousAt
  change ContinuousAt ((fun p : EReal × EReal ↦ p.1 - p.2) ∘ (fun x ↦ (c, x))) x
  exact (EReal.continuousAt_sub h'.symm (Or.inl hc_top)).comp (by fun_prop)

lemma EReal.continuousAt_sub_const {c x : EReal} (h' : x ≠ ⊥ ∨ c ≠ ⊥) :
    ContinuousAt (fun x : EReal ↦ x - c) x := by
  by_cases hc_top : c = ⊤
  · simp [hc_top]
    exact continuous_const.continuousAt
  change ContinuousAt ((fun p : EReal × EReal ↦ p.1 - p.2) ∘ (fun x ↦ (x, c))) x
  exact (EReal.continuousAt_sub (Or.inr hc_top) h').comp (by fun_prop)

lemma EReal.continuous_coe_mul {c : ℝ} : Continuous (fun x : EReal ↦ c * x) := by
  by_cases hc0 : c = 0
  · simp only [hc0, EReal.coe_zero, zero_mul]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x
  have h_cont : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (c, x) := by
    refine EReal.continuousAt_mul ?_ ?_ ?_ ?_ <;> exact Or.inl (by simp [hc0])
  refine h_cont.comp ?_
  fun_prop

@[simp]
lemma frontier_singleton {X : Type*} [TopologicalSpace X] [T1Space X] (x : X) [(𝓝[≠] x).NeBot] :
    frontier {x} = {x} := by simp [frontier]

lemma EReal.continuous_toENNReal : Continuous EReal.toENNReal := by
  refine continuous_if' ?_ ?_ ?_ ?_
  · simp only [setOf_eq_eq_singleton]
    intro a ha
    simp only [frontier_singleton, mem_singleton_iff] at ha
    simp [ha]
  · intro a ha
    simp only [setOf_eq_eq_singleton, frontier_singleton, mem_singleton_iff] at ha
    simp only [ha, ↓reduceIte, tendsto_ofReal_nhds_top]
    exact EReal.tendsto_toReal_atTop
  · fun_prop
  · intro x hx
    by_cases hx_bot : x = ⊥
    · simp only [hx_bot]
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      simp only [EReal.toReal_bot, ofReal_zero]
      suffices (fun x : EReal ↦ ofReal x.toReal) =ᶠ[𝓝 ⊥] fun _ ↦ 0 from
        EventuallyEq.filter_mono this nhdsWithin_le_nhds
      rw [EventuallyEq, eventually_nhds_iff]
      refine ⟨Iio 0, fun y hy ↦ ?_, isOpen_Iio, by simp⟩
      rw [ENNReal.ofReal_eq_zero]
      exact EReal.toReal_nonpos hy.le
    refine ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt ?_
    refine ContinuousAt.continuousWithinAt ?_
    refine EReal.continuousOn_toReal.continuousAt ?_
    rw [← EReal.range_coe, EReal.range_coe_eq_Ioo, mem_nhds_iff]
    exact ⟨Ioo ⊥ ⊤, subset_rfl, isOpen_Ioo, ⟨Ne.bot_lt hx_bot, Ne.lt_top hx⟩⟩

lemma EReal.tendsto_atTop_toENNReal : Tendsto EReal.toENNReal atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b, fun a hba ↦ ?_⟩
  have : b = (b : EReal).toENNReal := by simp
  rw [this]
  exact EReal.toENNReal_le_toENNReal hba

end EReal


/-! ### Basic properties of Stieltjes functions -/


/-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
structure ERealStieltjes where
  toFun : ℝ → EReal
  mono' : Monotone toFun
  right_continuous' : ∀ x, ContinuousWithinAt toFun (Ici x) x

def StieltjesFunction.erealStieltjes (f : StieltjesFunction) : ERealStieltjes where
  toFun := fun x ↦ f x
  mono' := sorry
  right_continuous' x := sorry

namespace ERealStieltjes

attribute [coe] toFun

instance instCoeFun : CoeFun ERealStieltjes fun _ => ℝ → EReal :=
  ⟨toFun⟩

initialize_simps_projections ERealStieltjes (toFun → apply)

@[ext] lemma ext {f g : ERealStieltjes} (h : ∀ x, f x = g x) : f = g := by
  exact (ERealStieltjes.mk.injEq ..).mpr (funext h)

variable (f : ERealStieltjes)

theorem mono : Monotone f :=
  f.mono'

theorem right_continuous (x : ℝ) : ContinuousWithinAt f (Ici x) x :=
  f.right_continuous' x

theorem rightLim_eq (f : ERealStieltjes) (x : ℝ) : Function.rightLim f x = f x := by
  rw [← f.mono.continuousWithinAt_Ioi_iff_rightLim_eq, continuousWithinAt_Ioi_iff_Ici]
  exact f.right_continuous' x

theorem iInf_Ioi_eq (f : ERealStieltjes) (x : ℝ) : ⨅ r : Ioi x, f r = f x := by
  suffices Function.rightLim f x = ⨅ r : Ioi x, f r by rw [← this, f.rightLim_eq]
  rw [f.mono.rightLim_eq_sInf, sInf_image']
  rw [← neBot_iff]
  infer_instance

-- theorem iInf_rat_gt_eq (f : ERealStieltjes) (x : ℝ) :
--     ⨅ r : { r' : ℚ // x < r' }, f r = f x := by
--   rw [← iInf_Ioi_eq f x]
--   refine (Real.iInf_Ioi_eq_iInf_rat_gt _ ?_ f.mono).symm
--   refine ⟨f x, fun y => ?_⟩
--   rintro ⟨y, hy_mem, rfl⟩
--   exact f.mono (le_of_lt hy_mem)

-- /-- The identity of `ℝ` as a Stieltjes function, used to construct Lebesgue measure. -/
-- @[simps]
-- protected def id : ERealStieltjes where
--   toFun := id
--   mono' _ _ := id
--   right_continuous' _ := continuousWithinAt_id

-- @[simp]
-- theorem id_leftLim (x : ℝ) : leftLim ERealStieltjes.id x = x :=
--   tendsto_nhds_unique (ERealStieltjes.id.mono.tendsto_leftLim x) <|
--     continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds

-- instance instInhabited : Inhabited ERealStieltjes :=
--   ⟨ERealStieltjes.id⟩

/-- Constant functions are Stieltjes function. -/
protected def const (c : EReal) : ERealStieltjes where
  toFun := fun _ ↦ c
  mono' _ _ := by simp
  right_continuous' _ := continuousWithinAt_const

@[simp] lemma const_apply (c : EReal) (x : ℝ) : ERealStieltjes.const c x = c := rfl

instance : Zero ERealStieltjes where
  zero := ERealStieltjes.const 0

@[simp] lemma zero_apply (x : ℝ) : (0 : ERealStieltjes) x = 0 := rfl

/-- The sum of two Stieltjes functions is a Stieltjes function. -/
protected def add (f g : ERealStieltjes) : ERealStieltjes where
  toFun := fun x => -(- f x - g x)  -- to ensure right continuity
  mono' x y hxy := by
    rw [EReal.neg_le_neg_iff]
    refine EReal.sub_le_sub ?_ (g.mono hxy)
    rw [EReal.neg_le_neg_iff]
    exact f.mono hxy
  right_continuous' x := by
    have hf := (f.right_continuous x).neg
    have hg := (g.right_continuous x).neg
    refine ContinuousWithinAt.neg ?_
    rw [ContinuousWithinAt] at hf hg ⊢
    simp_rw [sub_eq_add_neg]
    by_cases hf_top : f x = ⊤
    · simp only [hf_top, EReal.neg_top, EReal.bot_add]
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      have hfy : f y = ⊤ := eq_top_mono (f.mono hy) hf_top
      simp [hfy]
    by_cases hg_top : g x = ⊤
    · simp only [hg_top, EReal.neg_top, EReal.add_bot]
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      have hgy : g y = ⊤ := eq_top_mono (g.mono hy) hg_top
      simp [hgy]
    have hf_bot : - f x ≠ ⊥ := by simp [hf_top]
    have hg_bot : - g x ≠ ⊥ := by simp [hg_top]
    have h_tendsto : ContinuousAt (fun (p : EReal × EReal) ↦ p.1 + p.2) (-f x, -g x) :=
      EReal.continuousAt_add (Or.inr hg_bot) (Or.inl hf_bot)
    rw [ContinuousAt] at h_tendsto
    change Tendsto ((fun p : EReal × EReal ↦ p.1 + p.2) ∘ (fun x ↦ (-f x, -g x)))
      (𝓝[≥] x) (𝓝 (-f x + -g x))
    exact h_tendsto.comp <| Tendsto.prod_mk_nhds hf hg

instance : Add ERealStieltjes where
  add := ERealStieltjes.add

@[simp] lemma add_apply (f g : ERealStieltjes) (x : ℝ) : (f + g) x = - (-f x - g x) := rfl

lemma add_apply_of_ne_top {f g : ERealStieltjes} {x : ℝ} (hfx : f x ≠ ⊤) (hgx : g x ≠ ⊤) :
    (f + g) x = f x + g x := by
  rw [add_apply, EReal.neg_sub (Or.inl _) (Or.inr hgx), neg_neg]
  simp [hfx]

lemma add_apply_of_eq_top_left {f g : ERealStieltjes} {x : ℝ} (hfx : f x = ⊤) :
    (f + g) x = ⊤ := by
  simp [add_apply, hfx]

lemma add_apply_of_eq_top_right {f g : ERealStieltjes} {x : ℝ}  (hgx : g x = ⊤) :
    (f + g) x = ⊤ := by
  simp [add_apply, hgx]

instance : AddZeroClass ERealStieltjes where
  zero_add _ := by ext; simp
  add_zero _ := by ext; simp

instance : AddCommMonoid ERealStieltjes where
  nsmul n f := nsmulRec n f
  add_assoc f g h := ext fun x ↦ by
    by_cases hfx : f x = ⊤
    · rw [add_apply_of_eq_top_left, add_apply_of_eq_top_left hfx]
      rw [add_apply_of_eq_top_left hfx]
    by_cases hgx : g x = ⊤
    · rw [add_apply_of_eq_top_left, add_apply_of_eq_top_right]
      · rw [add_apply_of_eq_top_left hgx]
      · rw [add_apply_of_eq_top_right hgx]
    by_cases hhx : h x = ⊤
    · rw [add_apply_of_eq_top_right hhx, add_apply_of_eq_top_right]
      rw [add_apply_of_eq_top_right hhx]
    rw [add_apply_of_ne_top _ hhx, add_apply_of_ne_top hfx hgx, add_apply_of_ne_top hfx,
      add_apply_of_ne_top hgx hhx, add_assoc]
    · rw [add_apply_of_ne_top hgx hhx, ne_eq, EReal.add_eq_top_iff]
      simp [hgx, hhx]
    · rw [add_apply_of_ne_top hfx hgx, ne_eq, EReal.add_eq_top_iff]
      simp [hfx, hgx]
  add_comm f g := ext fun x ↦ by
    by_cases hfx : f x = ⊤
    · rw [add_apply_of_eq_top_left hfx, add_apply_of_eq_top_right hfx]
    by_cases hgx : g x = ⊤
    · rw [add_apply_of_eq_top_left hgx, add_apply_of_eq_top_right hgx]
    rw [add_apply_of_ne_top hfx hgx, add_apply_of_ne_top hgx hfx, add_comm]
  __ := ERealStieltjes.instAddZeroClass

instance : SMul ℝ≥0 ERealStieltjes where
  smul c f := {
    toFun := fun x ↦ c * f x
    mono' := by
      refine f.mono.const_mul ?_
      norm_cast
      exact zero_le'
    right_continuous' := fun x ↦
      EReal.continuous_coe_mul.continuousAt.comp_continuousWithinAt (f.right_continuous x)}

@[simp]
lemma smul_apply (c : ℝ≥0) (f : ERealStieltjes) {x : ℝ} : (c • f) x = c * f x := rfl

instance : Module ℝ≥0 ERealStieltjes where
  smul c f := c • f
  one_smul _ := ext fun _ ↦ one_mul _
  mul_smul a b f := ext fun x ↦ by
    simp only [smul_apply, coe_mul, EReal.coe_ennreal_mul]
    rw [mul_assoc]
  smul_zero _ := ext fun _ ↦ mul_zero _
  smul_add c f g  := ext fun x ↦ by
    simp only [smul_apply, add_apply, mul_neg, neg_inj]
    have : (c : EReal) = ((c : ℝ) : EReal) := rfl
    simp_rw [this]
    rw [sub_eq_add_neg, EReal.coe_mul_add_of_nonneg]
    swap; · exact c.2
    rw [mul_comm  _ (f x), ← EReal.neg_mul, mul_comm]
    congr 1
    rw [mul_comm _ (g x), ← EReal.neg_mul, mul_comm]
  add_smul a b f := ext fun x ↦ by
    by_cases ha0 : a = 0
    · simp [ha0]
    by_cases hfx : f x = ⊤
    · rw [smul_apply, hfx, add_apply_of_eq_top_left]
      · have : ((a + b : ℝ≥0) : EReal) = ((a + b : ℝ) : EReal) := rfl
        rw [this, EReal.coe_mul_top_of_pos]
        positivity
      · have : (a : EReal) = ((a : ℝ) : EReal) := rfl
        rw [smul_apply, hfx, this, EReal.coe_mul_top_of_pos]
        positivity
    rw [add_apply_of_ne_top]
    · simp only [smul_apply, coe_add, EReal.coe_ennreal_add]
      have h_eq (a : ℝ≥0) : (a : EReal) = ((a : ℝ) : EReal) := rfl
      rw [h_eq, h_eq, EReal.coe_add_mul_of_nonneg]
      · positivity
      · positivity
    · have : (a : EReal) = ((a : ℝ) : EReal) := rfl
      rw [smul_apply, this, EReal.mul_ne_top]
      simp [hfx]
    · have : (b : EReal) = ((b : ℝ) : EReal) := rfl
      rw [smul_apply, this, EReal.mul_ne_top]
      simp [hfx]
  zero_smul _ := ext fun _ ↦ zero_mul _

theorem countable_leftLim_ne (f : ERealStieltjes) : Set.Countable { x | leftLim f x ≠ f x } := by
  refine Countable.mono ?_ f.mono.countable_not_continuousAt
  intro x hx h'x
  apply hx
  exact tendsto_nhds_unique (f.mono.tendsto_leftLim x) (h'x.tendsto.mono_left nhdsWithin_le_nhds)

/-! ### The outer measure associated to a Stieltjes function -/


/-- Length of an interval. This is the largest monotone function which correctly measures all
intervals. -/
def length (s : Set ℝ) : ℝ≥0∞ :=
  ⨅ (a) (b) (_ : s ⊆ Ioc a b), (f b - f a).toENNReal

@[simp]
theorem length_empty : f.length ∅ = 0 :=
  nonpos_iff_eq_zero.1 <| iInf_le_of_le 0 <| iInf_le_of_le 0 <| by
  simp only [lt_self_iff_false, not_false_eq_true, Ioc_eq_empty, subset_refl, iInf_pos,
    nonpos_iff_eq_zero]
  rw [EReal.toENNReal_eq_zero_iff]
  exact EReal.sub_self_le_zero

@[simp]
theorem length_Ioc (a b : ℝ) : f.length (Ioc a b) = (f b - f a).toENNReal := by
  refine le_antisymm (iInf_le_of_le a <| iInf₂_le b Subset.rfl)
      (le_iInf fun a' ↦ le_iInf fun b' ↦ le_iInf fun h ↦ ?_)
  rcases le_or_lt b a with ab | ab
  · rw [EReal.toENNReal_of_nonpos (EReal.sub_nonpos.mpr (f.mono ab))]
    exact zero_le'
  refine EReal.toENNReal_le_toENNReal ?_
  cases' (Ioc_subset_Ioc_iff ab).1 h with h₁ h₂
  exact EReal.sub_le_sub (f.mono h₁) (f.mono h₂)

theorem length_mono {s₁ s₂ : Set ℝ} (h : s₁ ⊆ s₂) : f.length s₁ ≤ f.length s₂ :=
  iInf_mono fun _ ↦ biInf_mono fun _ ↦ h.trans

open MeasureTheory

open Classical in
/-- The Stieltjes outer measure associated to a Stieltjes function. -/
protected def outer : OuterMeasure ℝ :=
  OuterMeasure.ofFunction f.length f.length_empty

lemma outer_def : f.outer = OuterMeasure.ofFunction f.length f.length_empty := rfl

theorem outer_le_length (s : Set ℝ) : f.outer s ≤ f.length s :=
  OuterMeasure.ofFunction_le _

-- todo: generalize to ofFunction_mono
lemma outer_mono {s t : Set ℝ} (hst : s ⊆ t) : f.outer s ≤ f.outer t := by
  rw [outer_def, OuterMeasure.ofFunction_apply, OuterMeasure.ofFunction_apply]
  exact le_iInf₂ (fun ts hts ↦ iInf₂_le ts (hst.trans hts))

/-- If a compact interval `[a, b]` is covered by a union of open interval `(c i, d i)`, then
`f b - f a ≤ ∑ f (d i) - f (c i)`. This is an auxiliary technical statement to prove the same
statement for half-open intervals, the point of the current statement being that one can use
compactness to reduce it to a finite sum, and argue by induction on the size of the covering set. -/
theorem length_subadditive_Icc_Ioo {a b : ℝ} {c d : ℕ → ℝ} (ss : Icc a b ⊆ ⋃ i, Ioo (c i) (d i)) :
    (f b - f a).toENNReal ≤ ∑' i, (f (d i) - f (c i)).toENNReal := by
  suffices
    ∀ (s : Finset ℕ) (b), Icc a b ⊆ (⋃ i ∈ (s : Set ℕ), Ioo (c i) (d i)) →
      (f b - f a).toENNReal ≤ ∑ i ∈ s, (f (d i) - f (c i)).toENNReal by
    rcases isCompact_Icc.elim_finite_subcover_image
        (fun (i : ℕ) (_ : i ∈ univ) => @isOpen_Ioo _ _ _ _ (c i) (d i)) (by simpa using ss) with
      ⟨s, _, hf, hs⟩
    have e : ⋃ i ∈ (hf.toFinset : Set ℕ), Ioo (c i) (d i) = ⋃ i ∈ s, Ioo (c i) (d i) := by
      simp only [Set.ext_iff, exists_prop, Finset.set_biUnion_coe, mem_iUnion, forall_const,
        Finite.mem_toFinset]
    rw [ENNReal.tsum_eq_iSup_sum]
    refine le_trans ?_ (le_iSup _ hf.toFinset)
    exact this hf.toFinset _ (by simpa only [e] )
  clear ss b
  refine fun s => Finset.strongInductionOn s fun s IH b cv => ?_
  rcases le_total b a with ab | ab
  · rw [EReal.toENNReal_of_nonpos (EReal.sub_nonpos.2 (f.mono ab))]
    exact zero_le _
  have := cv ⟨ab, le_rfl⟩
  simp only [Finset.mem_coe, gt_iff_lt, not_lt, mem_iUnion, mem_Ioo, exists_and_left,
    exists_prop] at this
  rcases this with ⟨i, cb, is, bd⟩
  rw [← Finset.insert_erase is] at cv ⊢
  rw [Finset.coe_insert, biUnion_insert] at cv
  rw [Finset.sum_insert (Finset.not_mem_erase _ _)]
  refine le_trans ?_ (add_le_add_left (IH _ (Finset.erase_ssubset is) (c i) ?_) _)
  · refine (EReal.toENNReal_sub_le_add _ _ (f (c i))).trans ?_
    gcongr
    exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub (f.mono bd.le) le_rfl)
  · rintro x ⟨h₁, h₂⟩
    exact (cv ⟨h₁, le_trans h₂ (le_of_lt cb)⟩).resolve_left (mt And.left (not_lt_of_le h₂))

lemma continuousWithinAt_sub_const_Ici {c : EReal} {a : ℝ} (h_bot : f a ≠ ⊥ ∨ c ≠ ⊥) :
    ContinuousWithinAt (fun x ↦ f x - c) (Ici a) a :=
  (EReal.continuousAt_sub_const h_bot).comp_continuousWithinAt (f.right_continuous a)

lemma continuousWithinAt_const_sub_Ici {c : EReal} {a : ℝ} (h_bot : f a ≠ ⊤ ∨ c ≠ ⊤) :
    ContinuousWithinAt (fun x ↦ c - f x) (Ici a) a :=
  (EReal.continuousAt_const_sub h_bot).comp_continuousWithinAt (f.right_continuous a)

lemma continuousWithinAt_sub_const_Ioi {c : EReal} {a : ℝ} (h_bot : f a ≠ ⊥ ∨ c ≠ ⊥) :
    ContinuousWithinAt (fun x ↦ f x - c) (Ioi a) a :=
  (f.continuousWithinAt_sub_const_Ici h_bot).mono Ioi_subset_Ici_self

theorem outer_Ioc_of_ne_bot (a b : ℝ) (ha : f a ≠ ⊥) :
    f.outer (Ioc a b) = (f b - f a).toENNReal := by
  /- It suffices to show that, if `(a, b]` is covered by sets `s i`, then `f b - f a` is bounded
    by `∑ f.length (s i) + ε`. The difficulty is that `f.length` is expressed in terms of half-open
    intervals, while we would like to have a compact interval covered by open intervals to use
    compactness and finite sums, as provided by `length_subadditive_Icc_Ioo`. The trick is to use
    the right-continuity of `f`. If `a'` is close enough to `a` on its right, then `[a', b]` is
    still covered by the sets `s i` and moreover `f b - f a'` is very close to `f b - f a`
    (up to `ε/2`).
    Also, by definition one can cover `s i` by a half-closed interval `(p i, q i]` with `f`-length
    very close to that of `s i` (within a suitably small `ε' i`, say). If one moves `q i` very
    slightly to the right, then the `f`-length will change very little by right continuity, and we
    will get an open interval `(p i, q' i)` covering `s i` with `f (q' i) - f (p i)` within `ε' i`
    of the `f`-length of `s i`. -/
  refine le_antisymm ((f.length_Ioc _ _).symm ▸ outer_le_length _ _) ?_
  refine le_iInf₂ fun s' hs' ↦ ENNReal.le_of_forall_pos_le_add fun ε εpos h' ↦ ?_
  -- We ensure that `f x ≥ f a > ⊥` for all points in the sets `s i`
  let s : ℕ → Set ℝ := fun i ↦ s' i ∩ Ioc a b
  have hsab i : s i ⊆ Ioc a b := inter_subset_right
  have hs : Ioc a b = ⋃ i, s i := by
    rw [← iUnion_inter]
    simp [hs']
  have h : ∑' i, f.length (s i) < ⊤ := by
    refine (tsum_mono ENNReal.summable ENNReal.summable fun n ↦ ?_).trans_lt h'
    exact f.length_mono inter_subset_left
  suffices (f b - f a).toENNReal ≤ ∑' i, f.length (s i) + ε by
    refine this.trans ?_
    gcongr with i
    exact f.length_mono inter_subset_left
  -- we can w.l.o.g. assume that `f a ≠ ⊤`
  by_cases ha_top : f a = ⊤
  · simp [sub_eq_add_neg, ha_top]
  -- main case
  let δ := ε / 2
  have δpos : 0 < (δ : ℝ≥0∞) := by simpa [δ] using εpos.ne'
  rcases ENNReal.exists_pos_sum_of_countable δpos.ne' ℕ with ⟨ε', ε'0, hε⟩
  obtain ⟨a', ha', aa'⟩ : ∃ a', f a' - f a < δ ∧ a < a' := by
    have A : ContinuousWithinAt (fun r ↦ f r - f a) (Ioi a) a := by
      refine f.continuousWithinAt_sub_const_Ioi (.inl ha)
    have B : f a - f a < δ := by
      rw [EReal.sub_self ha_top ha]
      exact mod_cast δpos
    exact (((tendsto_order.1 A).2 _ B).and self_mem_nhdsWithin).exists
  have : ∀ i, ∃ p : ℝ × ℝ, s i ⊆ Ioo p.1 p.2
      ∧ (f p.2 - f p.1).toENNReal < f.length (s i) + ε' i := by
    intro i
    have hl :=
      ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_ne_zero.2 (ε'0 i).ne')
    conv at hl =>
      lhs
      rw [length]
    simp only [iInf_lt_iff, exists_prop] at hl
    rcases hl with ⟨p, q', spq, hq'⟩
    have hqa (h : q' ≤ a) : s i = ∅ := by
      have : s i ⊆ Ioc p q' ∩ Ioc a b := by simp [spq, hsab]
      rw [← subset_empty_iff]
      refine this.trans (subset_empty_iff.mpr ?_)
      rw [Ioc_inter_Ioc, Ioc_eq_empty]
      simp [h]
    classical
    let p'' := if s i = ∅ then a else p
    let q'' := if s i = ∅ then a else q'
    have hq''a : a ≤ q'' := by
      unfold_let q''
      split_ifs with h_empty
      · simp [h_empty]
      · have h : ¬q' ≤ a := hqa.mt h_empty
        exact (not_le.mp h).le
    have spq'' : s i ⊆ Ioc p'' q'' := by
      unfold q'' p''
      split_ifs with h_empty <;> simp [h_empty, spq]
    have hq'' : (f q'' - f p'').toENNReal < f.length (s i) + ↑(ε' i) := by
      unfold p'' q''
      split_ifs with h_empty
      rw [EReal.sub_self ha_top ha]
      · simp only [ne_eq, EReal.zero_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
        EReal.toReal_zero, ofReal_zero, add_pos_iff, ENNReal.coe_pos]
        exact .inr (ε'0 i)
      · exact hq'
    have : ContinuousWithinAt (fun r => (f r - f p'').toENNReal) (Ioi q'') q'' := by
      refine EReal.continuous_toENNReal.continuousAt.comp_continuousWithinAt ?_
      refine f.continuousWithinAt_sub_const_Ioi ?_
      exact .inl <| ne_of_gt (ha.bot_lt.trans_le (f.mono hq''a))
    rcases (((tendsto_order.1 this).2 _ hq'').and self_mem_nhdsWithin).exists with ⟨q, hq, q'q⟩
    exact ⟨⟨p'', q⟩, spq''.trans (Ioc_subset_Ioo_right q'q), hq⟩
  choose g hg using this
  have I_subset : Icc a' b ⊆ ⋃ i, Ioo (g i).1 (g i).2 :=
    calc
      Icc a' b ⊆ Ioc a b := fun x hx => ⟨aa'.trans_le hx.1, hx.2⟩
      _ = ⋃ i, s i := hs
      _ ⊆ ⋃ i, Ioo (g i).1 (g i).2 := iUnion_mono fun i => (hg i).1
  calc
    (f b - f a).toENNReal ≤ (f b - f a').toENNReal + (f a' - f a).toENNReal :=
        EReal.toENNReal_sub_le_add _ _ _
    _ ≤ ∑' i, (f (g i).2 - f (g i).1).toENNReal + ofReal δ := by
      refine (add_le_add (f.length_subadditive_Icc_Ioo I_subset) ?_)
      exact EReal.toENNReal_le_toENNReal ha'.le
    _ ≤ ∑' i, (f.length (s i) + ε' i) + δ :=
      (add_le_add (ENNReal.tsum_le_tsum fun i => (hg i).2.le)
        (by simp only [ENNReal.ofReal_coe_nnreal, le_rfl]))
    _ = ∑' i, f.length (s i) + ∑' i, (ε' i : ℝ≥0∞) + δ := by rw [ENNReal.tsum_add]
    _ ≤ ∑' i, f.length (s i) + δ + δ := add_le_add (add_le_add le_rfl hε.le) le_rfl
    _ = ∑' i : ℕ, f.length (s i) + ε := by simp [δ, add_assoc, ENNReal.add_halves]

theorem outer_Ioc_of_eq_bot (a b : ℝ) (hb : f b = ⊥) : f.outer (Ioc a b) = 0 := by
  refine le_antisymm ?_ zero_le'
  suffices f.outer (Ioc a b) ≤ (f b - f a).toENNReal by simpa [hb] using this
  exact (f.length_Ioc _ _).symm ▸ outer_le_length _ _

lemma iSup_le_outer_Ioc (a b : ℝ) :
    ⨆ c, ⨆ (_ : a < c), f.outer (Ioc c b) ≤ f.outer (Ioc a b) :=
  iSup₂_le fun _ hc ↦ f.outer_mono (Ioc_subset_Ioc hc.le le_rfl)

lemma outer_Ioc_eq_top_aux1 {a b : ℝ} (ha : f a = ⊥) (ha' : ∀ x, a < x → f x ≠ ⊥) (hab : a < b) :
    f.outer (Ioc a b) = ∞ := by
  refine eq_top_iff.mpr (le_trans ?_ (iSup_le_outer_Ioc _ _ _))
  have h_outer {b c} (hac : a < c) : f.outer (Ioc c b) = (f b - f c).toENNReal := by
    rw [outer_Ioc_of_ne_bot _ _ _ (ha' c hac)]
  have : ⨆ (c : ℝ) (_ : a < c), f.outer (Ioc c b)
      = ⨆ (c : ℝ) (_ : a < c), (f b - f c).toENNReal := by
    congr with c
    congr with hc
    rw [h_outer hc]
  rw [this]
  obtain ⟨c, _, hc_gt, hc_tendsto⟩ := exists_seq_strictAnti_tendsto' hab
  have h_tendsto : Tendsto (fun n ↦ (f b - f (c n)).toENNReal) atTop (𝓝 ⊤) := by
    have hc_tendsto' : Tendsto c atTop (𝓝[≥] a) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hc_tendsto, .of_forall fun n ↦ (hc_gt n).1.le⟩
    have h'' := continuousWithinAt_const_sub_Ici f (c := f b) (a := a) ?_
    swap; · simp [ha]
    have h := h''.tendsto.comp hc_tendsto'
    have h_eq_top : f b - f a = ⊤ := by
      rw [ha, sub_eq_add_neg, EReal.neg_bot, EReal.add_top_of_ne_bot (ha' b hab)]
    rw [h_eq_top] at h
    refine (EReal.continuous_toENNReal.tendsto _).comp h
  simp only [top_le_iff]
  refine eq_top_of_forall_nnreal_le fun r ↦ ?_
  simp_rw [ENNReal.tendsto_nhds_top_iff_nnreal, eventually_atTop] at h_tendsto
  obtain ⟨n, hn⟩ := h_tendsto r
  refine (hn n le_rfl).le.trans ?_
  exact le_iSup₂ (f := fun c _ ↦ (f b - f c).toENNReal) (c n) (hc_gt n).1

lemma outer_singleton_eq_top' {b : ℝ} (hb : ∀ a < b, f b - f a = ∞) :
    f.outer {b} = ∞ := by
  rw [outer_def, OuterMeasure.ofFunction_apply]
  simp only [iInf_eq_top]
  intro s hs
  refine ENNReal.tsum_eq_top_of_eq_top ?_
  simp_rw [length]
  simp only [iInf_eq_top, EReal.toENNReal_eq_top_iff]
  obtain ⟨n, hn⟩ : ∃ n, b ∈ s n := by
    rw [← mem_iUnion]
    exact hs (mem_singleton _)
  refine ⟨n, fun i j h_subset ↦ ?_⟩
  have hbij : b ∈ Ioc i j := h_subset hn
  refine eq_top_mono ?_ (hb i hbij.1)
  refine EReal.sub_le_sub (f.mono hbij.2) le_rfl

lemma outer_singleton_eq_top {b : ℝ} (hb : f b - leftLim f b = ∞) :
    f.outer {b} = ∞ := by
  refine outer_singleton_eq_top' f fun a ha ↦ ?_
  exact eq_top_mono (EReal.sub_le_sub le_rfl (f.mono.le_leftLim ha)) hb

lemma outer_singleton_aux {b : ℝ} (ha' : ∀ x < b, f x = ⊥) (hb : f b ≠ ⊥) :
    f.outer {b} = ∞ := by
  refine outer_singleton_eq_top f ?_
  have : leftLim f b = ⊥ := by
    refine leftLim_eq_of_tendsto NeBot.ne' ?_
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    rw [EventuallyEq, eventually_nhdsWithin_iff]
    exact .of_forall ha'
  rw [this, sub_eq_add_neg, EReal.neg_bot, EReal.add_top_of_ne_bot hb]
  simp

lemma outer_Ioc_eq_top_aux2 {a b : ℝ} (ha' : ∀ x < b, f x = ⊥) (hb : f b ≠ ⊥) (hab : a < b) :
    f.outer (Ioc a b) = ∞ :=
  eq_top_mono (f.outer_mono (singleton_subset_iff.mpr ⟨hab, le_rfl⟩)) (outer_singleton_aux f ha' hb)

@[simp]
theorem outer_Ioc (a b : ℝ) : f.outer (Ioc a b) = (f b - f a).toENNReal := by
  by_cases ha_bot : f a = ⊥
  swap; · exact outer_Ioc_of_ne_bot f a b ha_bot
  simp [ha_bot, sub_eq_add_neg]
  by_cases hb : f b = ⊥
  · simp [hb, outer_Ioc_of_eq_bot]
  rw [EReal.add_top_of_ne_bot hb, EReal.toENNReal_top]
  let a' := sSup {x | f x = ⊥}
  have hb_gt x (hx : f x = ⊥) : x < b := by
    have hxb : f x < f b := by
        rw [hx, bot_lt_iff_ne_bot]
        exact hb
    by_contra h_not
    exact not_le.mpr hxb (f.mono (not_lt.mp h_not))
  have ha'_lt x (hx : x < a') : f x = ⊥ := by
    obtain ⟨x', hx'_eq : f x' = ⊥, hxx'⟩ := exists_lt_of_lt_csSup ⟨a, ha_bot⟩ hx
    exact eq_bot_mono (f.mono hxx'.le) hx'_eq
  have ha'_gt x (hx : a' < x) : f x ≠ ⊥ := by
    by_contra! h_bot
    refine not_le.mpr hx ?_
    exact le_csSup ⟨b, fun x hx ↦ (hb_gt x hx).le⟩ h_bot
  have haa' : a ≤ a' := le_csSup ⟨b, fun x hx ↦ (hb_gt x hx).le⟩ ha_bot
  by_cases hfa' : f a' = ⊥
  · suffices f.outer (Ioc a' b) = ∞ from
      eq_top_mono (f.outer_mono (Ioc_subset_Ioc haa' le_rfl)) this
    exact outer_Ioc_eq_top_aux1 f hfa' ha'_gt (hb_gt a' hfa')
  · suffices f.outer (Ioc a a') = ∞ by
      refine eq_top_mono ?_ this
      refine f.outer_mono (Ioc_subset_Ioc le_rfl ?_)
      refine csSup_le ⟨a, ha_bot⟩ fun x hx ↦ (hb_gt x hx).le
    refine outer_Ioc_eq_top_aux2 f ha'_lt hfa' ?_
    exact lt_of_le_of_ne haa' fun h_eq ↦ (h_eq ▸ hfa') ha_bot

theorem measurableSet_Ioi {c : ℝ} : MeasurableSet[f.outer.caratheodory] (Ioi c) := by
  refine OuterMeasure.ofFunction_caratheodory fun t => ?_
  refine le_iInf fun a => le_iInf fun b => le_iInf fun h => ?_
  refine
    le_trans
      (add_le_add (f.length_mono <| inter_subset_inter_left _ h)
        (f.length_mono <| diff_subset_diff_left h)) ?_
  rcases le_total a c with hac | hac <;> rcases le_total b c with hbc | hbc
  · simp only [Ioc_inter_Ioi, f.length_Ioc, hac, _root_.sup_eq_max, hbc, le_refl, Ioc_eq_empty,
      max_eq_right, min_eq_left, Ioc_diff_Ioi, f.length_empty, zero_add, not_lt]
  · simp only [Ioc_inter_Ioi, hac, sup_of_le_right, length_Ioc, Ioc_diff_Ioi, hbc, min_eq_right]
    rw [← EReal.toENNReal_sub_eq_add (f.mono hac) (f.mono hbc)]
  · simp only [hbc, le_refl, Ioc_eq_empty, Ioc_inter_Ioi, min_eq_left, Ioc_diff_Ioi, f.length_empty,
      zero_add, or_true, le_sup_iff, f.length_Ioc, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right, _root_.sup_eq_max,
      le_refl, Ioc_eq_empty, add_zero, max_eq_left, f.length_empty, not_lt]

theorem outer_trim : f.outer.trim = f.outer := by
  refine le_antisymm (fun s => ?_) (OuterMeasure.le_trim _)
  rw [OuterMeasure.trim_eq_iInf]
  refine le_iInf fun t => le_iInf fun ht => ENNReal.le_of_forall_pos_le_add fun ε ε0 h => ?_
  rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 ε0).ne' ℕ with ⟨ε', ε'0, hε⟩
  refine le_trans ?_ (add_le_add_left (le_of_lt hε) _)
  rw [← ENNReal.tsum_add]
  choose g hg using
    show ∀ i, ∃ s, t i ⊆ s ∧ MeasurableSet s ∧ f.outer s ≤ f.length (t i) + ofReal (ε' i) by
      intro i
      have hl :=
        ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_pos.2 (ε'0 i)).ne'
      conv at hl =>
        lhs
        rw [length]
      simp only [iInf_lt_iff] at hl
      rcases hl with ⟨a, b, h₁, h₂⟩
      rw [← f.outer_Ioc] at h₂
      exact ⟨_, h₁, measurableSet_Ioc, le_of_lt <| by simpa using h₂⟩
  simp only [ofReal_coe_nnreal] at hg
  apply iInf_le_of_le (iUnion g) _
  apply iInf_le_of_le (ht.trans <| iUnion_mono fun i => (hg i).1) _
  apply iInf_le_of_le (MeasurableSet.iUnion fun i => (hg i).2.1) _
  exact le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun i => (hg i).2.2)

theorem borel_le_measurable : borel ℝ ≤ f.outer.caratheodory := by
  rw [borel_eq_generateFrom_Ioi]
  refine MeasurableSpace.generateFrom_le ?_
  simp (config := { contextual := true }) [f.measurableSet_Ioi]

/-! ### The measure associated to a Stieltjes function -/


/-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
interval `(a, b]`. -/
protected irreducible_def measure : Measure ℝ where
  toOuterMeasure := f.outer
  m_iUnion _s hs := f.outer.iUnion_eq_of_caratheodory fun i => f.borel_le_measurable _ (hs i)
  trim_le := f.outer_trim.le

@[simp]
theorem measure_Ioc (a b : ℝ) : f.measure (Ioc a b) = (f b - f a).toENNReal := by
  rw [ERealStieltjes.measure]
  exact f.outer_Ioc a b

lemma antitone_toENNReal_const_sub (a : ℝ) :
    Antitone (fun x ↦ (f a - f x).toENNReal) :=
  fun _ _ hxy ↦ EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl (f.mono hxy))

-- This is different from `(f a - leftLim f a).toENNReal` iff `f a = ⊤`, `leftLim f a = ⊤` but
-- `∀ x < a, f x < ⊤`.
@[simp]
theorem measure_singleton (a : ℝ) :
    f.measure {a} = leftLim (fun x ↦ (f a - f x).toENNReal) a := by
  by_cases h_top : ∀ x < a, f a - f x = ⊤
  · rw [f.measure_def]
    change f.outer {a} = _
    rw [outer_singleton_eq_top']
    · symm
      refine leftLim_eq_of_tendsto NeBot.ne' ?_
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      refine eventually_nhdsWithin_of_forall fun x hx ↦ ?_
      simp [h_top x hx]
    · convert h_top
  obtain ⟨u, u_mono, u_lt_a, u_lim⟩ :
    ∃ u : ℕ → ℝ, StrictMono u ∧ (∀ n : ℕ, u n < a) ∧ Tendsto u atTop (𝓝 a) :=
    exists_seq_strictMono_tendsto a
  have h_anti : Antitone (fun x ↦ (f a - f x).toENNReal) := antitone_toENNReal_const_sub f a
  have hu_tendsto_sub : Tendsto (fun n ↦ (f a - f (u n)).toENNReal) atTop
      (𝓝 (leftLim (fun x ↦ (f a - f x).toENNReal) a)) := by
    have h_ll := h_anti.tendsto_leftLim a
    have u_lim' : Tendsto u atTop (𝓝[<] a) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨u_lim, .of_forall u_lt_a⟩
    exact h_ll.comp u_lim'
  have A : {a} = ⋂ n, Ioc (u n) a := by
    refine Subset.antisymm (fun x hx ↦ by simp [mem_singleton_iff.1 hx, u_lt_a]) fun x hx ↦ ?_
    simp? at hx says simp only [mem_iInter, mem_Ioc] at hx
    have : a ≤ x := le_of_tendsto' u_lim fun n ↦ (hx n).1.le
    simp [le_antisymm this (hx 0).2]
  have L1 : Tendsto (fun n ↦ f.measure (Ioc (u n) a)) atTop (𝓝 (f.measure {a})) := by
    rw [A]
    refine tendsto_measure_iInter (fun n ↦ nullMeasurableSet_Ioc) (fun m n hmn ↦ ?_) ?_
    · exact Ioc_subset_Ioc_left (u_mono.monotone hmn)
    · simp_rw [measure_Ioc, ne_eq, EReal.toENNReal_eq_top_iff]
      by_contra! h
      simp only [h, EReal.toENNReal_top, tendsto_const_nhds_iff] at hu_tendsto_sub
      refine h_top fun x hx ↦ ?_
      suffices (f a - f x).toENNReal = ⊤ by rwa [EReal.toENNReal_eq_top_iff] at this
      refine eq_top_mono ?_ hu_tendsto_sub.symm
      exact h_anti.leftLim_le hx
  have L2 : Tendsto (fun n ↦ f.measure (Ioc (u n) a)) atTop
      (𝓝 (leftLim (fun x ↦ (f a - f x).toENNReal) a)) := by
    simp only [measure_Ioc]
    exact hu_tendsto_sub
  exact tendsto_nhds_unique L1 L2

-- This is different from `(f b - leftLim f a).toENNReal` iff `f b = ⊤`, `leftLim f a = ⊤` but
-- `∀ x < a, f x < ⊤`.
@[simp]
theorem measure_Icc (a b : ℝ) :
    f.measure (Icc a b) = leftLim (fun x ↦ (f b - f x).toENNReal) a := by
  rcases le_or_lt a b with (hab | hab)
  · have A : Disjoint {a} (Ioc a b) := by simp
    simp only [← Icc_union_Ioc_eq_Icc le_rfl hab, Icc_self, measure_union A measurableSet_Ioc,
      measure_singleton, measure_Ioc]
    rw [add_comm]
    calc (f b - f a).toENNReal + leftLim (fun x ↦ (f a - f x).toENNReal) a
    _ = leftLim (fun x ↦ (f b - f a).toENNReal + (f a - f x).toENNReal) a := by
      symm
      refine leftLim_eq_of_tendsto NeBot.ne' ?_
      refine Tendsto.const_add _ ?_
      exact (antitone_toENNReal_const_sub f a).tendsto_leftLim _
    _ = leftLim (fun x ↦ (f b - f x).toENNReal) a := by
      refine leftLim_eq_of_tendsto NeBot.ne' ?_
      have h := (antitone_toENNReal_const_sub f b).tendsto_leftLim a
      refine (tendsto_congr' ?_).mpr h
      refine eventually_nhdsWithin_of_forall fun x hx ↦ ?_
      simp only
      rw [← EReal.toENNReal_sub_eq_add]
      · exact f.mono hx.le
      · exact f.mono hab
  · simp only [hab, measure_empty, Icc_eq_empty, not_le]
    symm
    refine leftLim_eq_of_tendsto NeBot.ne' ?_
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    have : ∀ᶠ x in 𝓝[<] a, b < x := by
      refine eventually_nhdsWithin_iff.mpr ?_
      filter_upwards [eventually_gt_nhds hab] with x hx _ using hx
    filter_upwards [this] with x hx
    rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
    exact f.mono hx.le

@[simp]
theorem measure_Ioo {a b : ℝ} : f.measure (Ioo a b) = (leftLim f b - f a).toENNReal := by
  rcases le_or_lt b a with (hab | hab)
  · simp only [not_lt, hab, Ioo_eq_empty, measure_empty]
    symm
    rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
    exact f.mono.leftLim_le hab
  · have A : Disjoint (Ioo a b) {b} := by simp
    by_cases h_bot : leftLim f b = ⊥
    · have hfa : f a = ⊥ := by
        sorry
      sorry
    have D : f b - f a = f b - leftLim f b + (leftLim f b - f a) := by
      sorry
    have := f.measure_Ioc a b
    simp only [← Ioo_union_Icc_eq_Ioc hab le_rfl, measure_singleton,
      measure_union A (measurableSet_singleton b), Icc_self] at this
    rw [D, ENNReal.ofReal_add, add_comm] at this
    · simpa only [ENNReal.add_right_inj ENNReal.ofReal_ne_top]
    · simp only [f.mono.leftLim_le le_rfl, sub_nonneg]
    · simp only [f.mono.le_leftLim hab, sub_nonneg]

@[simp]
theorem measure_Ico (a b : ℝ) : f.measure (Ico a b) = (leftLim f b - leftLim f a).toENNReal := by
  rcases le_or_lt b a with (hab | hab)
  · simp only [hab, measure_empty, Ico_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim hab]
  · have A : Disjoint {a} (Ioo a b) := by simp
    simp [← Icc_union_Ioo_eq_Ico le_rfl hab, -singleton_union, hab.ne, f.mono.leftLim_le,
      measure_union A measurableSet_Ioo, f.mono.le_leftLim hab, ← ENNReal.ofReal_add]

theorem measure_Iic {l : EReal} (hf : Tendsto f atBot (𝓝 l)) (x : ℝ) :
    f.measure (Iic x) = (f x - l).toENNReal := by
  refine tendsto_nhds_unique (tendsto_measure_Ioc_atBot _ _) ?_
  simp_rw [measure_Ioc]
  exact ENNReal.tendsto_ofReal (Tendsto.const_sub _ hf)

theorem measure_Ici {l : EReal} (hf : Tendsto f atTop (𝓝 l)) (x : ℝ) :
    f.measure (Ici x) = (l - leftLim f x).toENNReal := by
  refine tendsto_nhds_unique (tendsto_measure_Ico_atTop _ _) ?_
  simp_rw [measure_Ico]
  refine ENNReal.tendsto_ofReal (Tendsto.sub_const ?_ _)
  have h_le1 : ∀ x, f (x - 1) ≤ leftLim f x := fun x => Monotone.le_leftLim f.mono (sub_one_lt x)
  have h_le2 : ∀ x, leftLim f x ≤ f x := fun x => Monotone.leftLim_le f.mono le_rfl
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hf.comp ?_) hf h_le1 h_le2
  rw [tendsto_atTop_atTop]
  exact fun y => ⟨y + 1, fun z hyz => by rwa [le_sub_iff_add_le]⟩

theorem measure_univ {l u : EReal} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    f.measure univ = (u - l).toENNReal := by
  refine tendsto_nhds_unique (tendsto_measure_Iic_atTop _) ?_
  simp_rw [measure_Iic f hfl]
  exact ENNReal.tendsto_ofReal (Tendsto.sub_const hfu _)

lemma isFiniteMeasure {l u : ℝ} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    IsFiniteMeasure f.measure := by
  constructor
  simp only [f.measure_univ hfl hfu]
  rw [lt_top_iff_ne_top, ne_eq, EReal.toENNReal_eq_top_iff, ← EReal.coe_sub]
  exact EReal.coe_ne_top _

lemma isProbabilityMeasure (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) :
    IsProbabilityMeasure f.measure := ⟨by simp [f.measure_univ hf_bot hf_top]⟩

-- instance instIsLocallyFiniteMeasure : IsLocallyFiniteMeasure f.measure :=
--   ⟨fun x => ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), by simp⟩⟩

lemma eq_of_measure_of_tendsto_atBot (g : ERealStieltjes) {l : ℝ}
    (hfg : f.measure = g.measure) (hfl : Tendsto f atBot (𝓝 l)) (hgl : Tendsto g atBot (𝓝 l)) :
    f = g := by
  ext x
  have hf := measure_Iic f hfl x
  rw [hfg, measure_Iic g hgl x, EReal.toENNReal_eq_toENNReal_iff, eq_comm] at hf
  · simpa using hf
  · rw [EReal.sub_nonneg (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    exact Monotone.le_of_tendsto g.mono hgl x
  · rw [EReal.sub_nonneg (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    exact Monotone.le_of_tendsto f.mono hfl x

@[simp]
lemma measure_const (c : ℝ) : (ERealStieltjes.const c).measure = 0 :=
  Measure.ext_of_Ioc _ _ (fun _ _ _ ↦ by simp)

@[simp]
lemma measure_add (f g : ERealStieltjes) : (f + g).measure = f.measure + g.measure := by
  refine Measure.ext_of_Ioc _ _ (fun a b h ↦ ?_)
  simp only [measure_Ioc, add_apply, Measure.coe_add, Pi.add_apply]
  rw [← ENNReal.ofReal_add (sub_nonneg_of_le (f.mono h.le)) (sub_nonneg_of_le (g.mono h.le))]
  ring_nf

@[simp]
lemma measure_smul (c : ℝ≥0) (f : ERealStieltjes) : (c • f).measure = c • f.measure := by
  refine Measure.ext_of_Ioc _ _ (fun a b _ ↦ ?_)
  simp only [measure_Ioc, Measure.smul_apply]
  change ofReal (c * f b - c * f a) = c • ofReal (f b - f a)
  rw [← _root_.mul_sub, ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal, ← smul_eq_mul]
  rfl

end ERealStieltjes

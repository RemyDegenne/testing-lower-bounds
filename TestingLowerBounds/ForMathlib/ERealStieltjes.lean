/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Order.LeftRightLim
public import TestingLowerBounds.ForMathlib.EReal
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

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

@[expose] public section

noncomputable section

open Set Filter Function ENNReal NNReal Topology MeasureTheory

/-! ### Basic properties of Stieltjes functions -/

/-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
structure ERealStieltjes where
  /-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
  toFun : ℝ → EReal
  mono' : Monotone toFun
  right_continuous' : ∀ x, ContinuousWithinAt toFun (Ici x) x

namespace ERealStieltjes

attribute [coe] toFun

instance instCoeFun : CoeFun ERealStieltjes fun _ ↦ ℝ → EReal where
  coe := toFun

initialize_simps_projections ERealStieltjes (toFun → apply)

@[ext] lemma ext {f g : ERealStieltjes} (h : ∀ x, f x = g x) : f = g :=
  (ERealStieltjes.mk.injEq ..).mpr (funext h)

variable (f : ERealStieltjes)

theorem mono : Monotone f := f.mono'

theorem right_continuous (x : ℝ) : ContinuousWithinAt f (Ici x) x := f.right_continuous' x

/-- If a function `f : ℝ → EReal` is monotone, then the function mapping `x` to the right limit of
`f` at `x` is an `ERealStieltjes` function, i.e., it is monotone and right-continuous.
This is the `EReal` analogue of `Monotone.stieltjesFunction`. -/
noncomputable def _root_.Monotone.erealStieltjes {g : ℝ → EReal} (hg : Monotone g) :
    ERealStieltjes where
  toFun := Function.rightLim g
  mono' := hg.rightLim
  right_continuous' x := continuousWithinAt_rightLim_Ici (hg.tendsto_rightLim x)

theorem _root_.Monotone.erealStieltjes_eq {g : ℝ → EReal} (hg : Monotone g) (x : ℝ) :
    hg.erealStieltjes x = Function.rightLim g x := rfl

theorem rightLim_eq (f : ERealStieltjes) (x : ℝ) : Function.rightLim f x = f x := by
  rw [← f.mono.continuousWithinAt_Ioi_iff_rightLim_eq, continuousWithinAt_Ioi_iff_Ici]
  exact f.right_continuous' x

theorem iInf_Ioi_eq (f : ERealStieltjes) (x : ℝ) : ⨅ r : Ioi x, f r = f x := by
  suffices Function.rightLim f x = ⨅ r : Ioi x, f r by rw [← this, f.rightLim_eq]
  rw [f.mono.rightLim_eq_sInf, sInf_image']

/-- Constant functions are Stieltjes function. -/
protected def const (c : EReal) : ERealStieltjes where
  toFun := fun _ ↦ c
  mono' _ _ := by simp
  right_continuous' _ := continuousWithinAt_const

@[simp] lemma const_apply (c : EReal) (x : ℝ) : ERealStieltjes.const c x = c := rfl

instance : Zero ERealStieltjes where
  zero := ERealStieltjes.const 0

@[simp] lemma zero_apply (x : ℝ) : (0 : ERealStieltjes) x = 0 := rfl

instance : Inhabited ERealStieltjes where
  default := 0

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
    exact h_tendsto.comp <| Tendsto.prodMk_nhds hf hg

instance : Add ERealStieltjes where
  add := ERealStieltjes.add

lemma add_apply (f g : ERealStieltjes) (x : ℝ) : (f + g) x = - (-f x - g x) := rfl

lemma add_apply_of_ne_top {f g : ERealStieltjes} {x : ℝ} (hfx : f x ≠ ⊤) (hgx : g x ≠ ⊤) :
    (f + g) x = f x + g x := by
  rw [add_apply, EReal.neg_sub (Or.inl _) (Or.inr hgx), neg_neg]
  simp [hfx]

lemma add_apply_of_eq_top_left {f g : ERealStieltjes} {x : ℝ} (hfx : f x = ⊤) :
    (f + g) x = ⊤ := by
  simp [add_apply, hfx]

lemma add_apply_of_eq_top_right {f g : ERealStieltjes} {x : ℝ} (hgx : g x = ⊤) :
    (f + g) x = ⊤ := by
  simp [add_apply, hgx]

instance : AddZeroClass ERealStieltjes where
  zero_add _ := by ext; simp [add_apply]
  add_zero _ := by ext; simp [add_apply]

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
      exact zero_le
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
    rw [sub_eq_add_neg, EReal.left_distrib_of_nonneg_of_ne_top (x := ((c : ℝ) : EReal))]
    rotate_left
    · exact EReal.coe_nonneg.mpr c.2
    · exact EReal.coe_ne_top _
    rw [mul_comm  _ (f x), ← EReal.neg_mul, mul_comm]
    congr 1
    rw [mul_comm _ (g x), ← EReal.neg_mul, mul_comm]
  add_smul a b f := ext fun x ↦ by
    by_cases ha0 : a = 0
    · simp [ha0, add_apply]
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
      rw [h_eq, h_eq, EReal.right_distrib_of_nonneg]
      · exact EReal.coe_nonneg.mpr a.2
      · exact EReal.coe_nonneg.mpr b.2
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

section EffectiveDomain

/-- Lower bound of the set on which `f` is not `⊥`. -/
def xmin : ℝ := sInf {y | f y ≠ ⊥}

/-- Upper bound of the set on which `f` is not `⊤`. -/
def xmax : ℝ := sSup {y | f y ≠ ⊤}

end EffectiveDomain

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
  rcases le_or_gt b a with ab | ab
  · rw [EReal.toENNReal_of_nonpos (EReal.sub_nonpos.mpr (f.mono ab))]
    exact zero_le
  refine EReal.toENNReal_le_toENNReal ?_
  obtain ⟨h₁, h₂⟩ := (Ioc_subset_Ioc_iff ab).1 h
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
      simp only [Finset.set_biUnion_coe, Finite.mem_toFinset]
    rw [ENNReal.tsum_eq_iSup_sum]
    refine le_trans ?_ (le_iSup _ hf.toFinset)
    exact this hf.toFinset _ (by simpa only [e] )
  clear ss b
  refine fun s => Finset.strongInductionOn s fun s IH b cv => ?_
  rcases le_total b a with ab | ab
  · rw [EReal.toENNReal_of_nonpos (EReal.sub_nonpos.2 (f.mono ab))]
    exact zero_le
  have := cv ⟨ab, le_rfl⟩
  simp only [Finset.mem_coe, mem_iUnion, mem_Ioo, exists_and_left, exists_prop] at this
  rcases this with ⟨i, cb, is, bd⟩
  rw [← Finset.insert_erase is] at cv ⊢
  rw [Finset.coe_insert, biUnion_insert] at cv
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  refine le_trans ?_ (add_le_add_right (IH _ (Finset.erase_ssubset is) (c i) ?_) _)
  · refine (EReal.toENNReal_sub_le_add _ _ (f (c i))).trans ?_
    gcongr
    exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub (f.mono bd.le) le_rfl)
  · rintro x ⟨h₁, h₂⟩
    exact (cv ⟨h₁, le_trans h₂ (le_of_lt cb)⟩).resolve_left (mt And.left (not_lt_of_ge h₂))

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
    refine (ENNReal.tsum_le_tsum fun n ↦ ?_).trans_lt h'
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
      unfold q''
      split_ifs with h_empty
      · simp
      · have h : ¬q' ≤ a := hqa.mt h_empty
        exact (not_le.mp h).le
    have spq'' : s i ⊆ Ioc p'' q'' := by
      unfold q'' p''
      split_ifs with h_empty <;> simp [h_empty, spq]
    have hq'' : (f q'' - f p'').toENNReal < f.length (s i) + ↑(ε' i) := by
      unfold p'' q''
      split_ifs with h_empty
      · rw [EReal.sub_self ha_top ha]
        simp only [ne_eq, EReal.zero_ne_top, not_false_eq_true, EReal.toENNReal_of_ne_top,
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
    _ ≤ ∑' i, (f (g i).2 - f (g i).1).toENNReal + ENNReal.ofReal δ := by
      refine (add_le_add (f.length_subadditive_Icc_Ioo I_subset) ?_)
      exact EReal.toENNReal_le_toENNReal ha'.le
    _ ≤ ∑' i, (f.length (s i) + ε' i) + δ :=
      (add_le_add (ENNReal.tsum_le_tsum fun i => (hg i).2.le)
        (by simp only [ENNReal.ofReal_coe_nnreal, le_rfl]))
    _ = ∑' i, f.length (s i) + ∑' i, (ε' i : ℝ≥0∞) + δ := by rw [ENNReal.tsum_add]
    _ ≤ ∑' i, f.length (s i) + δ + δ := add_le_add (add_le_add le_rfl hε.le) le_rfl
    _ = ∑' i : ℕ, f.length (s i) + ε := by simp [δ, add_assoc, ENNReal.add_halves]

theorem outer_Ioc_of_eq_bot (a b : ℝ) (hb : f b = ⊥) : f.outer (Ioc a b) = 0 := by
  refine le_antisymm ?_ zero_le
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
    refine leftLim_eq_of_tendsto ?_
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
  simp only [ha_bot, sub_eq_add_neg, EReal.neg_bot]
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
        (f.length_mono <| sdiff_subset_sdiff_left h)) ?_
  rcases le_total a c with hac | hac <;> rcases le_total b c with hbc | hbc
  · simp only [Ioc_inter_Ioi, f.length_Ioc, hac, hbc, le_refl, Ioc_eq_empty,
      max_eq_right, min_eq_left, Ioc_sdiff_Ioi, f.length_empty, zero_add, not_lt]
  · simp only [Ioc_inter_Ioi, hac, sup_of_le_right, length_Ioc, Ioc_sdiff_Ioi, hbc, min_eq_right]
    rw [EReal.toENNReal_sub_add_cancel (f.mono hac) (f.mono hbc)]
  · simp only [hbc, le_refl, Ioc_eq_empty, Ioc_inter_Ioi, min_eq_left, Ioc_sdiff_Ioi,
      f.length_empty, zero_add, or_true, le_sup_iff, f.length_Ioc, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_sdiff_Ioi, f.length_Ioc, min_eq_right,
      le_refl, Ioc_eq_empty, add_zero, max_eq_left, f.length_empty, not_lt]

theorem outer_trim : f.outer.trim = f.outer := by
  refine le_antisymm (fun s => ?_) (OuterMeasure.le_trim _)
  rw [OuterMeasure.trim_eq_iInf]
  refine le_iInf fun t => le_iInf fun ht => ENNReal.le_of_forall_pos_le_add fun ε ε0 h => ?_
  rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 ε0).ne' ℕ with ⟨ε', ε'0, hε⟩
  refine le_trans ?_ (add_le_add_right (le_of_lt hε) _)
  rw [← ENNReal.tsum_add]
  choose g hg using
    show ∀ i, ∃ s, t i ⊆ s ∧ MeasurableSet s
        ∧ f.outer s ≤ f.length (t i) + ENNReal.ofReal (ε' i) by
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
  m_iUnion _s hs := f.outer.iUnion_eq_of_caratheodory fun i ↦ f.borel_le_measurable _ (hs i)
  trim_le := f.outer_trim.le

@[simp]
theorem measure_Ioc (a b : ℝ) : f.measure (Ioc a b) = (f b - f a).toENNReal := by
  rw [ERealStieltjes.measure]
  exact f.outer_Ioc a b

lemma antitone_toENNReal_const_sub (a : ℝ) :
    Antitone (fun x ↦ (f a - f x).toENNReal) :=
  fun _ _ hxy ↦ EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl (f.mono hxy))

lemma leftLim_toENNReal_sub_left (a b : ℝ) :
    leftLim (fun x ↦ (f x - f a).toENNReal) b = (leftLim f b - f a).toENNReal := by
  rcases le_or_gt a b with (_ | hab)
  swap
  · refine leftLim_eq_of_tendsto ?_
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    have : ∀ᶠ x in 𝓝[<] b, x < a := by
      refine eventually_nhdsWithin_iff.mpr ?_
      filter_upwards [eventually_lt_nhds hab] with x hx _ using hx
    filter_upwards [this] with x hx
    rw [EReal.toENNReal_of_nonpos, EReal.toENNReal_of_nonpos]
    · rw [EReal.sub_nonpos]
      exact f.mono.leftLim_le hab.le
    · rw [EReal.sub_nonpos]
      exact f.mono hx.le
  by_cases hfa : f a = ⊥
  · simp only [hfa, sub_eq_add_neg, EReal.neg_bot]
    by_cases h_lim : leftLim f b = ⊥
    · simp only [h_lim, EReal.bot_add, ne_eq, bot_ne_top, not_false_eq_true,
        EReal.toENNReal_of_ne_top, EReal.toReal_bot, ofReal_zero]
      have h_lt x (hxb : x < b) : f x = ⊥ := eq_bot_mono (f.mono.le_leftLim hxb) h_lim
      refine leftLim_eq_of_tendsto ?_
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      refine eventually_nhdsWithin_of_forall fun x hx ↦ ?_
      simp [h_lt x hx]
    · rw [EReal.add_top_of_ne_bot h_lim, EReal.toENNReal_top]
      refine leftLim_eq_of_tendsto ?_
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      obtain ⟨x, hxb, hx⟩ : ∃ x < b, f x ≠ ⊥ := by
        by_contra! h_bot
        refine h_lim ?_
        refine leftLim_eq_of_tendsto ?_
        refine (tendsto_congr' ?_).mpr tendsto_const_nhds
        exact eventually_nhdsWithin_of_forall h_bot
      have : ∀ᶠ y in 𝓝[<] b, x < y := by
        refine eventually_nhdsWithin_iff.mpr ?_
        filter_upwards [eventually_gt_nhds hxb] with y hy _ using hy
      filter_upwards [this] with y hy
      rw [EReal.toENNReal_eq_top_iff, EReal.add_top_of_ne_bot]
      exact fun h_bot ↦ hx (eq_bot_mono (f.mono hy.le) h_bot)
  refine leftLim_eq_of_tendsto ?_
  have h1 := EReal.continuous_toENNReal.tendsto (leftLim f b - f a)
  have h2 := EReal.continuousAt_sub_const (c := f a) (x := leftLim f b) (Or.inr hfa)
  exact h1.comp <| h2.tendsto.comp <| f.mono.tendsto_leftLim _

lemma leftLim_toENNReal_sub_right (a : ℝ) (c : EReal)
    (h : c = ⊤ → leftLim f a = ⊤ → ∃ x < a, f x = ⊤) :
    leftLim (fun x ↦ (c - f x).toENNReal) a = (c - leftLim f a).toENNReal := by
  rcases le_or_gt (leftLim f a) c with (hab | hab)
  swap
  · refine leftLim_eq_of_tendsto ?_
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    have : ∀ᶠ x in 𝓝[<] a, c < f x :=
      Filter.Tendsto.eventually_const_lt hab (f.mono.tendsto_leftLim _)
    filter_upwards [this] with x hx
    rw [EReal.toENNReal_of_nonpos, EReal.toENNReal_of_nonpos]
    · rw [EReal.sub_nonpos]
      exact hab.le
    · rw [EReal.sub_nonpos]
      exact hx.le
  have h1 := EReal.continuous_toENNReal.tendsto (c - leftLim f a)
  have h2 := EReal.continuousAt_const_sub (c := c) (x := leftLim f a)
  by_cases hfb : c = ⊤
  swap
  · refine leftLim_eq_of_tendsto ?_
    refine h1.comp ?_
    refine (h2 (Or.inr hfb)).tendsto.comp ?_
    exact f.mono.tendsto_leftLim _
  specialize h hfb
  by_cases h_lim : leftLim f a = ⊤
  swap
  · refine leftLim_eq_of_tendsto ?_
    refine h1.comp ?_
    refine (h2 (Or.inl h_lim)).tendsto.comp ?_
    exact f.mono.tendsto_leftLim _
  specialize h h_lim
  obtain ⟨x, hx⟩ := h
  have hfa_lim : leftLim f a = ⊤ := eq_top_mono (f.mono.le_leftLim hx.1) hx.2
  have hfb : c = ⊤ := eq_top_mono hab hfa_lim
  simp only [hfb, hfa_lim, EReal.sub_top, ne_eq, bot_ne_top, not_false_eq_true,
    EReal.toENNReal_of_ne_top, EReal.toReal_bot, ofReal_zero]
  refine leftLim_eq_of_tendsto ?_
  refine (tendsto_congr' ?_).mpr tendsto_const_nhds
  have : ∀ᶠ y in 𝓝[<] a, x < y := by
    refine eventually_nhdsWithin_iff.mpr ?_
    filter_upwards [eventually_gt_nhds hx.1] with x hx _ using hx
  filter_upwards [this] with y hy
  rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos, ← eq_top_iff]
  refine eq_top_mono (f.mono hy.le) hx.2

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
      refine leftLim_eq_of_tendsto ?_
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      refine eventually_nhdsWithin_of_forall fun x hx ↦ ?_
      simp [h_top x hx]
    · convert h_top
      simp
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
    refine tendsto_measure_iInter_atTop (fun n ↦ nullMeasurableSet_Ioc) (fun m n hmn ↦ ?_) ?_
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
  rcases le_or_gt a b with (hab | hab)
  · have A : Disjoint {a} (Ioc a b) := by simp
    simp only [← Icc_union_Ioc_eq_Icc le_rfl hab, Icc_self, measure_union A measurableSet_Ioc,
      measure_singleton, measure_Ioc]
    rw [add_comm]
    calc (f b - f a).toENNReal + leftLim (fun x ↦ (f a - f x).toENNReal) a
    _ = leftLim (fun x ↦ (f b - f a).toENNReal + (f a - f x).toENNReal) a := by
      symm
      refine leftLim_eq_of_tendsto ?_
      refine Tendsto.const_add _ ?_
      exact (antitone_toENNReal_const_sub f a).tendsto_leftLim _
    _ = leftLim (fun x ↦ (f b - f x).toENNReal) a := by
      refine leftLim_eq_of_tendsto ?_
      have h := (antitone_toENNReal_const_sub f b).tendsto_leftLim a
      refine (tendsto_congr' ?_).mpr h
      refine eventually_nhdsWithin_of_forall fun x hx ↦ ?_
      simp only
      rw [EReal.toENNReal_sub_add_cancel]
      · exact f.mono hx.le
      · exact f.mono hab
  · simp only [hab, measure_empty, Icc_eq_empty, not_le]
    symm
    refine leftLim_eq_of_tendsto ?_
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    have : ∀ᶠ x in 𝓝[<] a, b < x := by
      refine eventually_nhdsWithin_iff.mpr ?_
      filter_upwards [eventually_gt_nhds hab] with x hx _ using hx
    filter_upwards [this] with x hx
    rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
    exact f.mono hx.le

@[simp]
theorem measure_Ioo {a b : ℝ} :
    f.measure (Ioo a b) = (leftLim f b - f a).toENNReal := by
  rw [← leftLim_toENNReal_sub_left]
  rcases le_or_gt b a with (hab | hab)
  · simp only [not_lt, hab, Ioo_eq_empty, measure_empty]
    symm
    refine leftLim_eq_of_tendsto ?_
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    refine eventually_nhdsWithin_of_forall fun x hx ↦ ?_
    simp only
    rw [EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
    exact f.mono (hx.le.trans hab)
  · obtain ⟨c, hc_mono, hc_mem, hc_tendsto⟩ := exists_seq_strictMono_tendsto' hab
    have h_iUnion : Ioo a b = ⋃ i, Ioc a (c i) := by
      ext x
      simp only [mem_Ioo, mem_iUnion, mem_Ioc, exists_and_left, and_congr_right_iff]
      refine fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · exact (Filter.Tendsto.eventually_const_le h hc_tendsto).exists
      · obtain ⟨n, hn⟩ := h
        exact hn.trans_lt (hc_mem _).2
    have h_mono : Monotone fun x ↦ (f x - f a).toENNReal :=
      fun _ _ hxy ↦ EReal.toENNReal_le_toENNReal (EReal.sub_le_sub (f.mono hxy) le_rfl)
    rw [h_iUnion, Monotone.measure_iUnion]
    · simp only [measure_Ioc]
      rw [Monotone.leftLim_eq_sSup h_mono]
      apply le_antisymm
      · refine iSup_le fun n ↦ ?_
        refine le_sSup ?_
        simp only [mem_image, mem_Iio]
        exact ⟨c n, (hc_mem _).2, rfl⟩
      · refine sSup_le fun y hy ↦ ?_
        simp only [mem_image, mem_Iio] at hy
        obtain ⟨x, hx_lt, rfl⟩ := hy
        have : ∀ᶠ i in atTop, x < c i := Filter.Tendsto.eventually_const_lt hx_lt hc_tendsto
        obtain ⟨n, hn⟩ := this.exists
        exact le_iSup_of_le n (h_mono hn.le)
    · intro i j hij x
      simp only [mem_Ioc, and_imp]
      intro hax hxc
      exact ⟨hax, hxc.trans (hc_mono.monotone hij)⟩

theorem measure_Ico_of_lt {a b : ℝ} (hab : a < b) :
    f.measure (Ico a b)
      = leftLim (fun x ↦ (f a - f x).toENNReal) a + (leftLim f b - f a).toENNReal := by
  have A : Disjoint {a} (Ioo a b) := by simp
  simp only [← Icc_union_Ioo_eq_Ico le_rfl hab, Icc_self, measure_union A measurableSet_Ioo,
    measure_singleton, measure_Ioo]

lemma measure_Ico_of_lt_of_eq_top {a b : ℝ} (hab : a < b)
    (h : f a = ⊤ → leftLim f a = ⊤ → ∃ x < a, f x = ⊤) :
    f.measure (Ico a b) = (leftLim f b - leftLim f a).toENNReal := by
  rw [measure_Ico_of_lt _ hab, leftLim_toENNReal_sub_right f _ _ h, add_comm,
    EReal.toENNReal_sub_add_cancel (f.mono.leftLim_le le_rfl) (f.mono.le_leftLim hab)]

lemma measure_Ico_of_ge {a b : ℝ} (hab : b ≤ a) : f.measure (Ico a b) = 0 := by simp [hab]

lemma measure_Ico_of_eq_top {a : ℝ}
    (h : f a = ⊤ → leftLim f a = ⊤ → ∃ x < a, f x = ⊤) (b : ℝ) :
    f.measure (Ico a b) = (leftLim f b - leftLim f a).toENNReal := by
  rcases le_or_gt b a with (hab | hab)
  · symm
    rw [measure_Ico_of_ge f hab, EReal.toENNReal_eq_zero_iff, EReal.sub_nonpos]
    exact f.mono.leftLim hab
  · rw [measure_Ico_of_lt_of_eq_top _ hab h]

theorem measure_Iic {l : EReal} (hf : Tendsto f atBot (𝓝 l)) (x : ℝ) :
    f.measure (Iic x) = (f x - l).toENNReal := by
  refine tendsto_nhds_unique (tendsto_measure_Ioc_atBot _ _) ?_
  simp_rw [measure_Ioc]
  by_cases h_top : l = ⊤
  · have : f = ERealStieltjes.const ⊤ := by
      ext x
      simp only [const_apply]
      have h := f.mono.le_of_tendsto hf
      simp only [h_top, top_le_iff] at h
      exact h x
    simp [this, h_top]
  · have h1 := EReal.continuous_toENNReal.tendsto (f x - l)
    have h2 := EReal.continuousAt_const_sub (c := f x) (x := l) (Or.inl h_top)
    exact h1.comp (h2.tendsto.comp hf)

theorem measure_Ici {l : EReal} (hf : Tendsto f atTop (𝓝 l)) (x : ℝ) :
    f.measure (Ici x) = leftLim (fun z ↦ (f x - f z).toENNReal) x + (l - f x).toENNReal := by
  refine tendsto_nhds_unique (tendsto_measure_Ico_atTop _ _) ?_
  have h_Ico : ∀ᶠ y in atTop, f.measure (Ico x y)
      = leftLim (fun z ↦ (f x - f z).toENNReal) x + (leftLim f y - f x).toENNReal := by
    filter_upwards [eventually_gt_atTop x] with y hy
    rw [measure_Ico_of_lt _ hy]
  rw [tendsto_congr' h_Ico]
  refine Tendsto.add tendsto_const_nhds ?_
  by_cases h_bot : l = ⊥
  · have : f = ERealStieltjes.const ⊥ := by
      ext x
      simp only [const_apply]
      have h := f.mono.ge_of_tendsto hf
      simp only [h_bot, le_bot_iff] at h
      exact h x
    have h_lim x : leftLim (ERealStieltjes.const ⊥) x = ⊥ := by
      refine eq_bot_mono ?_ (rfl : ERealStieltjes.const ⊥ x = ⊥)
      exact (ERealStieltjes.const ⊥).mono.leftLim_le le_rfl
    simp [this, h_bot, h_lim]
  · have h1 := EReal.continuous_toENNReal.tendsto (l - f x)
    refine h1.comp ?_
    have h2 := EReal.continuousAt_sub_const (c := f x) (x := l) (Or.inl h_bot)
    refine h2.tendsto.comp ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun x ↦ f (x - 1)) ?_ hf ?_ ?_
    · refine hf.comp ?_
      exact tendsto_atTop_add_const_right atTop (-1) fun _ a ↦ a
    · refine fun x ↦ f.mono.le_leftLim ?_
      linarith
    · exact fun x ↦ f.mono.leftLim_le le_rfl

lemma measure_Ici_of_eq_top {l : EReal} (hf : Tendsto f atTop (𝓝 l)) {x : ℝ}
    (h : f x = ⊤ → leftLim f x = ⊤ → ∃ y < x, f y = ⊤) :
    f.measure (Ici x) = (l - leftLim f x).toENNReal := by
  rw [measure_Ici f hf, leftLim_toENNReal_sub_right f _ _ h, add_comm,
    EReal.toENNReal_sub_add_cancel (f.mono.leftLim_le le_rfl) (f.mono.ge_of_tendsto hf x)]

lemma measure_Iio {l : EReal} (hf : Tendsto f atBot (𝓝 l)) (x : ℝ) :
    f.measure (Iio x) = leftLim (fun y ↦ (f y - l).toENNReal) x := by
  obtain ⟨c, hc_mono, hc_mem, hc_tendsto⟩ := exists_seq_strictMono_tendsto x
  have h_iUnion : Iio x = ⋃ i, Iic (c i) := by
    ext x
    simp only [mem_Iio, mem_iUnion, mem_Iic]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · exact (Filter.Tendsto.eventually_const_le h hc_tendsto).exists
    · obtain ⟨n, hn⟩ := h
      exact hn.trans_lt (hc_mem _)
  have h_mono : Monotone fun x ↦ (f x - l).toENNReal :=
    fun _ _ hxy ↦ EReal.toENNReal_le_toENNReal (EReal.sub_le_sub (f.mono hxy) le_rfl)
  rw [h_iUnion, Monotone.measure_iUnion]
  swap; · exact monotone_Iic.comp hc_mono.monotone
  simp only [measure_Iic f hf]
  rw [Monotone.leftLim_eq_sSup h_mono]
  apply le_antisymm
  · refine iSup_le fun n ↦ ?_
    refine le_sSup ?_
    simp only [mem_image, mem_Iio]
    exact ⟨c n, hc_mem _, rfl⟩
  · refine sSup_le fun y hy ↦ ?_
    simp only [mem_image, mem_Iio] at hy
    obtain ⟨x, hx_lt, rfl⟩ := hy
    have : ∀ᶠ i in atTop, x < c i := Filter.Tendsto.eventually_const_lt hx_lt hc_tendsto
    obtain ⟨n, hn⟩ := this.exists
    exact le_iSup_of_le n (h_mono hn.le)

theorem measure_univ {l u : EReal} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    f.measure univ = (u - l).toENNReal := by
  refine tendsto_nhds_unique (tendsto_measure_Iic_atTop _) ?_
  simp_rw [measure_Iic f hfl]
  by_cases h_top : l = ⊤
  · have : f = ERealStieltjes.const ⊤ := by
      ext x
      simp only [const_apply]
      have h := f.mono.le_of_tendsto hfl
      simp only [h_top, top_le_iff] at h
      exact h x
    simp [this, h_top]
  by_cases h_bot : u = ⊥
  · have : f = ERealStieltjes.const ⊥ := by
      ext x
      simp only [const_apply]
      have h := f.mono.ge_of_tendsto hfu
      simp only [h_bot, le_bot_iff] at h
      exact h x
    simp [this, h_bot]
  · have h1 := EReal.continuous_toENNReal.tendsto (u - l)
    have h2 := EReal.continuousAt_sub_const (c := l) (x := u) (Or.inl h_bot)
    refine h1.comp <| h2.tendsto.comp hfu

@[simp]
lemma measure_const (c : EReal) : (ERealStieltjes.const c).measure = 0 := by
  rw [← Measure.measure_univ_eq_zero, measure_univ (l := c) (u := c)]
  · induction c <;> simp
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds

lemma measure_Ioi {l : EReal} (hf : Tendsto f atTop (𝓝 l)) (x : ℝ) :
    f.measure (Ioi x) = (l - f x).toENNReal := by
  by_cases h_bot : l = ⊥
  · have : f = ERealStieltjes.const ⊥ := by
      ext x
      simp only [const_apply]
      have h := f.mono.ge_of_tendsto hf
      simp only [h_bot, le_bot_iff] at h
      exact h x
    simp [this, h_bot]
  obtain ⟨c, hc_mono, hc_tendsto⟩ := exists_seq_monotone_tendsto_atTop_atTop ℝ
  have h_iUnion : Ioi x = ⋃ i, Ioo x (c i) := by
    ext y
    simp only [mem_Ioi, mem_iUnion, mem_Ioo, exists_and_left, iff_self_and]
    refine fun h ↦ ?_
    rw [tendsto_atTop_atTop] at hc_tendsto
    obtain ⟨n, hn⟩ := hc_tendsto (y+1)
    exact ⟨n, (lt_add_one y).trans_le (hn n le_rfl)⟩
  rw [h_iUnion, Monotone.measure_iUnion]
  swap
  · intro i j hij y
    simp only [mem_Ioo, and_imp]
    exact fun hxy hxi ↦ ⟨hxy, hxi.trans_le (hc_mono hij)⟩
  simp only [measure_Ioo f]
  have h_tendsto : Tendsto (fun y ↦ (leftLim f y - f x).toENNReal) atTop
      (𝓝 (l - f x).toENNReal) := by
    have h1 := EReal.continuous_toENNReal.tendsto (l - f x)
    refine h1.comp ?_
    have h2 := EReal.continuousAt_sub_const (c := f x) (x := l) (Or.inl h_bot)
    refine h2.tendsto.comp ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun x ↦ f (x - 1)) ?_ hf ?_ ?_
    · refine hf.comp ?_
      exact tendsto_atTop_add_const_right atTop (-1) fun _ a ↦ a
    · refine fun x ↦ f.mono.le_leftLim ?_
      linarith
    · exact fun x ↦ f.mono.leftLim_le le_rfl
  rw [iSup_eq_of_tendsto]
  · exact fun _ _ hxy ↦ EReal.toENNReal_le_toENNReal
      (EReal.sub_le_sub (f.mono.leftLim (hc_mono hxy)) le_rfl)
  · exact h_tendsto.comp hc_tendsto

lemma measure_Ioi_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : ℝ) :
    f.measure (Ioi x) = (⊤ - f x).toENNReal := by
  have hf' : Tendsto f atTop (𝓝 ⊤) := by
    simp_rw [EReal.tendsto_nhds_top_iff_real, eventually_atTop]
    rw [tendsto_atTop_atTop] at hf
    intro x
    obtain ⟨y, hy⟩ := hf (x + 1)
    refine ⟨y, fun z hz ↦ lt_of_lt_of_le ?_ (hy z hz)⟩
    exact mod_cast (lt_add_one x)
  rw [measure_Ioi f hf']

@[simp]
lemma measure_zero : (0 : ERealStieltjes).measure = 0 := measure_const 0

section SFinite

lemma measure_Ioc_eq_zero_of_eq_bot {a b : ℝ} (ha : f a = ⊥) (hb : f b = ⊥) :
    f.measure (Ioc a b) = 0 := by
  rw [measure_Ioc, hb, ha, EReal.bot_sub, EReal.toENNReal_bot]

lemma measure_Ioc_eq_zero_of_eq_top {a b : ℝ} (ha : f a = ⊤) (hb : f b = ⊤) :
    f.measure (Ioc a b) = 0 := by
  rw [measure_Ioc, hb, ha, EReal.sub_top, EReal.toENNReal_bot]

lemma iUnion_Ioc_neg_nat_nat : ⋃ n : ℕ, Ioc (-(n : ℝ)) n = univ := by
  refine eq_univ_of_forall fun x ↦ mem_iUnion.mpr ?_
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  exact ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

lemma measure_eq_zero_of_forall_eq_bot (h : ∀ x, f x = ⊥) : f.measure = 0 := by
  refine Measure.measure_univ_eq_zero.mp ?_
  rw [← iUnion_Ioc_neg_nat_nat]
  exact measure_iUnion_null fun n ↦ f.measure_Ioc_eq_zero_of_eq_bot (h _) (h _)

lemma measure_eq_zero_of_forall_eq_top (h : ∀ x, f x = ⊤) : f.measure = 0 := by
  refine Measure.measure_univ_eq_zero.mp ?_
  rw [← iUnion_Ioc_neg_nat_nat]
  exact measure_iUnion_null fun n ↦ f.measure_Ioc_eq_zero_of_eq_top (h _) (h _)

lemma measure_Iio_eq_zero_of_forall_lt_eq_bot {c : ℝ} (h : ∀ x, x < c → f x = ⊥) :
    f.measure (Iio c) = 0 := by
  have : Iio c = ⋃ n : ℕ, Ioc (c - (n + 1)) (c - 1 / (n + 1)) := by
    ext y
    simp only [mem_Iio, mem_iUnion, mem_Ioc]
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hy)
      obtain ⟨m, hm⟩ := exists_nat_gt (c - y)
      refine ⟨max n m, ?_, ?_⟩
      · have : (m : ℝ) ≤ max n m := by exact_mod_cast le_max_right n m
        linarith
      · have : (1 : ℝ) / (max n m + 1) ≤ 1 / (n + 1) :=
          one_div_le_one_div_of_le (by positivity)
            (by exact_mod_cast Nat.add_le_add_right (le_max_left n m) 1)
        linarith
    · rintro ⟨n, _, hy⟩
      have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
  rw [this]
  refine measure_iUnion_null fun n ↦ f.measure_Ioc_eq_zero_of_eq_bot (h _ ?_) (h _ ?_)
  · have : (0 : ℝ) ≤ n + 1 := by positivity
    linarith
  · have : (0 : ℝ) < 1 / (n + 1) := by positivity
    linarith

lemma measure_Ioi_eq_zero_of_forall_gt_eq_top {d : ℝ} (h : ∀ x, d < x → f x = ⊤) :
    f.measure (Ioi d) = 0 := by
  have : Ioi d = ⋃ n : ℕ, Ioc (d + 1 / (n + 1)) (d + (n + 1)) := by
    ext y
    simp only [mem_Ioi, mem_iUnion, mem_Ioc]
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hy)
      obtain ⟨m, hm⟩ := exists_nat_gt (y - d)
      refine ⟨max n m, ?_, ?_⟩
      · have : (1 : ℝ) / (max n m + 1) ≤ 1 / (n + 1) :=
          one_div_le_one_div_of_le (by positivity)
            (by exact_mod_cast Nat.add_le_add_right (le_max_left n m) 1)
        linarith
      · have : (m : ℝ) ≤ max n m := by exact_mod_cast le_max_right n m
        linarith
    · rintro ⟨n, hy, _⟩
      have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
  rw [this]
  refine measure_iUnion_null fun n ↦ f.measure_Ioc_eq_zero_of_eq_top (h _ ?_) (h _ ?_)
  · have : (0 : ℝ) < 1 / (n + 1) := by positivity
    linarith
  · have : (0 : ℝ) ≤ n + 1 := by positivity
    linarith

/-- The restriction of `f.measure` to the region where `f` is `⊥`, together with its right
endpoint, is s-finite: that region is null except possibly for an infinite atom at its endpoint. -/
lemma sfinite_restrict_of_forall_lt_eq_bot (c : EReal) (h : ∀ x : ℝ, (x : EReal) < c → f x = ⊥) :
    SFinite (f.measure.restrict {x : ℝ | (x : EReal) ≤ c}) := by
  induction c with
  | bot =>
    have : {x : ℝ | (x : EReal) ≤ ⊥} = ∅ := by
      ext x
      simp
    rw [this, Measure.restrict_empty]
    infer_instance
  | coe c =>
    have : {x : ℝ | (x : EReal) ≤ c} = Iio c ∪ {c} := by
      ext x
      simp only [mem_ofPred_eq, EReal.coe_le_coe_iff, union_singleton, mem_insert_iff, mem_Iio]
      exact le_iff_eq_or_lt
    rw [this, Measure.restrict_union ((Set.disjoint_singleton_right (s := Iio c)).mpr (lt_irrefl c))
        (measurableSet_singleton _),
      Measure.restrict_eq_zero.mpr
        (f.measure_Iio_eq_zero_of_forall_lt_eq_bot fun x hx ↦ h x (EReal.coe_lt_coe_iff.mpr hx)),
      zero_add, Measure.restrict_singleton]
    infer_instance
  | top =>
    rw [f.measure_eq_zero_of_forall_eq_bot fun x ↦ h x (EReal.coe_lt_top x)]
    infer_instance

/-- The restriction of `f.measure` to the region where `f` is `⊤`, together with its left
endpoint, is s-finite: that region is null except possibly for an infinite atom at its endpoint. -/
lemma sfinite_restrict_of_forall_gt_eq_top (d : EReal) (h : ∀ x : ℝ, d < (x : EReal) → f x = ⊤) :
    SFinite (f.measure.restrict {x : ℝ | d ≤ (x : EReal)}) := by
  induction d with
  | bot =>
    rw [f.measure_eq_zero_of_forall_eq_top fun x ↦ h x (EReal.bot_lt_coe x)]
    infer_instance
  | coe d =>
    have : {x : ℝ | (d : EReal) ≤ x} = {d} ∪ Ioi d := by
      ext x
      simp only [mem_ofPred_eq, EReal.coe_le_coe_iff, singleton_union, mem_insert_iff, mem_Ioi]
      exact le_iff_eq_or_lt.trans (or_congr_left eq_comm)
    rw [this, Measure.restrict_union ((Set.disjoint_singleton_left (s := Ioi d)).mpr (lt_irrefl d))
        _root_.measurableSet_Ioi,
      Measure.restrict_eq_zero.mpr
        (f.measure_Ioi_eq_zero_of_forall_gt_eq_top fun x hx ↦ h x (EReal.coe_lt_coe_iff.mpr hx)),
      add_zero, Measure.restrict_singleton]
    infer_instance
  | top =>
    have : {x : ℝ | (⊤ : EReal) ≤ x} = ∅ := by
      ext x
      simp
    rw [this, Measure.restrict_empty]
    infer_instance

/-- The measure associated to an `ERealStieltjes` function is s-finite: it is σ-finite on the
(open) region where `f` is finite, vanishes where `f` is `⊥` or `⊤`, and has at most two
(possibly infinite) atoms at the boundary of that region. -/
instance : SFinite f.measure := by
  -- `c` bounds the region where `f = ⊥`, `d` the region where `f = ⊤`
  set c : EReal := sSup (Real.toEReal '' {x | f x = ⊥}) with hc
  set d : EReal := sInf (Real.toEReal '' {x | f x = ⊤}) with hd
  have hc_lt : ∀ x : ℝ, (x : EReal) < c → f x = ⊥ := by
    intro x hx
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := lt_sSup_iff.mp hx
    exact eq_bot_mono (f.mono (EReal.coe_lt_coe_iff.mp hxy).le) hy
  have hc_gt : ∀ x : ℝ, c < x → f x ≠ ⊥ := fun x hx h ↦
    (not_le.mpr hx) (le_sSup ⟨x, h, rfl⟩)
  have hd_gt : ∀ x : ℝ, d < x → f x = ⊤ := by
    intro x hx
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := sInf_lt_iff.mp hx
    exact eq_top_mono (f.mono (EReal.coe_lt_coe_iff.mp hxy).le) hy
  have hd_lt : ∀ x : ℝ, (x : EReal) < d → f x ≠ ⊤ := fun x hx h ↦
    (not_le.mpr hx) (sInf_le ⟨x, h, rfl⟩)
  -- the region where `f` is finite
  set M : Set ℝ := {x | c < x ∧ (x : EReal) < d} with hM
  have hM_open : IsOpen M :=
    (isOpen_lt continuous_const continuous_coe_real_ereal).inter
      (isOpen_lt continuous_coe_real_ereal continuous_const)
  have h_fin : ∀ x ∈ M, ∀ y ∈ M, f.measure (Ioc x y) ≠ ∞ := by
    intro x hx y hy
    have h3 : f y - f x ≠ ⊤ := by
      rw [sub_eq_add_neg]
      exact (EReal.add_ne_top_iff_ne_top₂ (hc_gt y hy.1) (by simpa using hd_lt x hx.2)).mpr
        ⟨hd_lt y hy.2, by simpa using hc_gt x hx.1⟩
    rw [measure_Ioc]
    exact fun h ↦ h3 (EReal.toENNReal_eq_top_iff.mp h)
  have h_sigma : SigmaFinite (f.measure.restrict M) := by
    refine Measure.sigmaFinite_of_countable
      (S := (fun p : ℚ × ℚ ↦ Ioc (p.1 : ℝ) p.2) '' {p | (p.1 : ℝ) ∈ M ∧ (p.2 : ℝ) ∈ M} ∪ {Mᶜ})
      (((Set.to_countable _).image _).union (countable_singleton _)) ?_ ?_
    · rintro s (⟨p, hp, rfl⟩ | rfl)
      · rw [Measure.restrict_apply measurableSet_Ioc]
        exact (measure_mono inter_subset_left).trans_lt (h_fin _ hp.1 _ hp.2).lt_top
      · rw [Measure.restrict_apply hM_open.measurableSet.compl]
        simp
    · refine eq_univ_of_forall fun x ↦ mem_sUnion.mpr ?_
      by_cases hx : x ∈ M
      · obtain ⟨a, b, hxab, habM⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hM_open.mem_nhds hx)
        obtain ⟨q, haq, hqx⟩ := exists_rat_btwn hxab.1
        obtain ⟨r, hxr, hrb⟩ := exists_rat_btwn hxab.2
        exact ⟨Ioc (q : ℝ) r, Or.inl ⟨(q, r), ⟨habM ⟨haq, hqx.trans hxab.2⟩,
          habM ⟨hxab.1.trans hxr, hrb⟩⟩, rfl⟩, hqx, hxr.le⟩
      · exact ⟨Mᶜ, Or.inr rfl, hx⟩
  -- assemble the pieces
  have hA := f.sfinite_restrict_of_forall_lt_eq_bot c hc_lt
  have hB := f.sfinite_restrict_of_forall_gt_eq_top d hd_gt
  have hA_meas : MeasurableSet {x : ℝ | (x : EReal) ≤ c} :=
    (isClosed_le continuous_coe_real_ereal continuous_const).measurableSet
  have hB_meas : MeasurableSet {x : ℝ | d ≤ (x : EReal)} :=
    (isClosed_le continuous_const continuous_coe_real_ereal).measurableSet
  have h1 : f.measure = f.measure.restrict {x : ℝ | (x : EReal) ≤ c}
      + f.measure.restrict {x : ℝ | (x : EReal) ≤ c}ᶜ :=
    (Measure.restrict_add_restrict_compl hA_meas).symm
  have h2 : f.measure.restrict {x : ℝ | (x : EReal) ≤ c}ᶜ
      = (f.measure.restrict {x : ℝ | (x : EReal) ≤ c}ᶜ).restrict {x : ℝ | d ≤ (x : EReal)}
        + (f.measure.restrict {x : ℝ | (x : EReal) ≤ c}ᶜ).restrict {x : ℝ | d ≤ (x : EReal)}ᶜ :=
    (Measure.restrict_add_restrict_compl hB_meas).symm
  have h3 : (f.measure.restrict {x : ℝ | (x : EReal) ≤ c}ᶜ).restrict {x : ℝ | d ≤ (x : EReal)}
      = (f.measure.restrict {x : ℝ | d ≤ (x : EReal)}).restrict {x : ℝ | (x : EReal) ≤ c}ᶜ := by
    rw [Measure.restrict_restrict hB_meas, Measure.restrict_restrict hA_meas.compl, inter_comm]
  have h4 : (f.measure.restrict {x : ℝ | (x : EReal) ≤ c}ᶜ).restrict {x : ℝ | d ≤ (x : EReal)}ᶜ
      = f.measure.restrict M := by
    rw [Measure.restrict_restrict hB_meas.compl]
    congr 1
    ext x
    simp [M, not_le, and_comm]
  have : SFinite (f.measure.restrict {x : ℝ | (x : EReal) ≤ c}ᶜ) := by
    rw [h2, h3, h4]
    infer_instance
  rw [h1]
  infer_instance

end SFinite

lemma isFiniteMeasure {l u : ℝ} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    IsFiniteMeasure f.measure := by
  constructor
  simp only [f.measure_univ hfl hfu]
  rw [lt_top_iff_ne_top, ne_eq, EReal.toENNReal_eq_top_iff, ← EReal.coe_sub]
  exact EReal.coe_ne_top _

lemma isProbabilityMeasure (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) :
    IsProbabilityMeasure f.measure := ⟨by simp [f.measure_univ hf_bot hf_top]⟩

lemma isLocallyFiniteMeasure (hf : ∀ x, f x ≠ ⊥ ∧ f x ≠ ⊤) :
    IsLocallyFiniteMeasure f.measure := by
  refine ⟨fun x ↦ ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (lt_add_one x), ?_⟩⟩
  rw [measure_Ioo, lt_top_iff_ne_top, EReal.toENNReal_ne_top_iff]
  simp only [sub_eq_add_neg, ne_eq, EReal.add_eq_top_iff, EReal.neg_eq_bot_iff,
    EReal.neg_eq_top_iff, not_or, not_and, Decidable.not_not]
  constructor
  · exact fun h ↦ absurd h <| ne_top_of_le_ne_top (hf _).2 (f.mono.leftLim_le le_rfl)
  · exact fun _ ↦ (hf _).1

lemma eq_of_measure_of_tendsto_atBot (g : ERealStieltjes) {l : ℝ}
    (hfg : f.measure = g.measure) (hfl : Tendsto f atBot (𝓝 l)) (hgl : Tendsto g atBot (𝓝 l)) :
    f = g := by
  ext x
  have hf := measure_Iic f hfl x
  rw [hfg, measure_Iic g hgl x, EReal.toENNReal_eq_toENNReal, eq_comm] at hf
  · calc f x = (f x - l) + l := by rw [sub_eq_add_neg, add_assoc, add_comm _ (l : EReal),
        ← sub_eq_add_neg, EReal.sub_self] <;> simp
    _ = (g x - l) + l := by rw [hf]
    _ = g x := by rw [sub_eq_add_neg, add_assoc, add_comm _ (l : EReal),
        ← sub_eq_add_neg, EReal.sub_self] <;> simp
  · rw [EReal.sub_nonneg (.inr (EReal.coe_ne_top _)) (.inr (EReal.coe_ne_bot _))]
    exact Monotone.le_of_tendsto g.mono hgl x
  · rw [EReal.sub_nonneg (.inr (EReal.coe_ne_top _)) (.inr (EReal.coe_ne_bot _))]
    exact Monotone.le_of_tendsto f.mono hfl x

lemma EReal.toENNReal_toEReal (x : ℝ) : EReal.toENNReal x = ENNReal.ofReal x := rfl

-- this is not enough. We need to remove hf and hg and deal with those issues properly.
-- The measure is then not locally finite because of the possible infinite diracs at xmin and xmax,
-- but we can cut the measure into several pieces to isolate the difficulties.
lemma measure_add (f g : ERealStieltjes) (hf : ∀ x, f x ≠ ⊥ ∧ f x ≠ ⊤)
    (hg : ∀ x, g x ≠ ⊥ ∧ g x ≠ ⊤) :
    (f + g).measure = f.measure + g.measure := by
  have hfg x : (f + g) x ≠ ⊥ ∧ (f + g) x ≠ ⊤ := by
    rw [add_apply_of_ne_top (hf x).2 (hg x).2]
    simp [EReal.add_eq_top_iff, hf x, hg x]
  have := ERealStieltjes.isLocallyFiniteMeasure _ hfg
  refine Measure.ext_of_Ioc _ _ (fun a b h ↦ ?_)
  simp only [measure_Ioc, Pi.add_apply, Measure.coe_add]
  rw [add_apply_of_ne_top (hf b).2 (hg b).2, add_apply_of_ne_top (hf a).2 (hg a).2]
  have hfab : f a ≤ f b := f.mono h.le
  have hgab : g a ≤ g b := g.mono h.le
  lift (f a) to ℝ using (hf a).symm with fa
  lift (f b) to ℝ using (hf b).symm with fb
  lift (g a) to ℝ using (hg a).symm with ga
  lift (g b) to ℝ using (hg b).symm with gb
  norm_cast
  simp_rw [EReal.toENNReal_toEReal]
  rw [← ENNReal.ofReal_add (sub_nonneg_of_le ?_) (sub_nonneg_of_le ?_)]
  rotate_left
  · exact mod_cast hfab
  · exact mod_cast hgab
  congr 1
  ring

end ERealStieltjes

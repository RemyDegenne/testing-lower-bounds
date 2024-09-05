/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.ForMathlib.LeftRightDeriv

/-!

# DerivAtTop

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open Real MeasureTheory Filter Set

open scoped ENNReal NNReal Topology

lemma EReal.tendsto_of_monotone {ι : Type*} [Preorder ι] {f : ι → EReal} (hf : Monotone f) :
    ∃ y, Tendsto f atTop (𝓝 y) :=
  ⟨_, tendsto_atTop_ciSup hf (OrderTop.bddAbove _)⟩

lemma EReal.tendsto_of_monotoneOn {ι : Type*} [SemilatticeSup ι] [Nonempty ι] {x : ι}
    {f : ι → EReal} (hf : MonotoneOn f (Ici x)) :
    ∃ y, Tendsto f atTop (𝓝 y) := by
  classical
  suffices ∃ y, Tendsto (fun z ↦ if x ≤ z then f z else f x) atTop (𝓝 y) by
    obtain ⟨y, hy⟩ := this
    refine ⟨y, ?_⟩
    refine (tendsto_congr' ?_).mp hy
    rw [EventuallyEq, eventually_atTop]
    exact ⟨x, fun z hz ↦ if_pos hz⟩
  refine EReal.tendsto_of_monotone (fun y z hyz ↦ ?_)
  split_ifs with hxy hxz hxz
  · exact hf hxy hxz hyz
  · exact absurd (hxy.trans hyz) hxz
  · exact hf le_rfl hxz hxz
  · exact le_rfl

lemma Real.monotone_toEReal : Monotone toEReal := Monotone.of_map_inf fun _ ↦ congrFun rfl

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {f g : ℝ → ℝ} {x : ℝ}

lemma ite_bot_ae_eq_atTop (f : ℝ → EReal) :
    (fun x ↦ if 1 ≤ x then f x else ⊥) =ᶠ[atTop] f := by
  rw [Filter.EventuallyEq, eventually_atTop]
  exact ⟨1, fun x hx ↦ by simp [hx]⟩

-- The constant 1 chosen here is an arbitrary number greater than 0.
lemma MonotoneOn.monotone_ite_bot (hf : MonotoneOn (rightDeriv f) (Ioi 0)) :
    Monotone (fun x ↦ if 1 ≤ x then (rightDeriv f x : EReal) else ⊥) := by
  intro x y hxy
  cases le_or_lt 1 x with
  | inl hx =>
    simp only [hx, hx.trans hxy, ↓reduceIte]
    norm_cast
    exact (hf.mono (Ici_subset_Ioi.mpr zero_lt_one)) hx (hx.trans hxy) hxy
  | inr hx =>
    simp only [not_le.mpr hx, ↓reduceIte, bot_le]

/-- Limsup of the right derivative at infinity. -/
noncomputable
def derivAtTop (f : ℝ → ℝ) : EReal := limsup (fun x ↦ (rightDeriv f x : EReal)) atTop

lemma derivAtTop_congr (h : f =ᶠ[atTop] g) : derivAtTop f = derivAtTop g := by
  simp_rw [derivAtTop]
  refine limsup_congr ?_
  filter_upwards [rightDeriv_congr_atTop h] with x hx
  rw [hx]

lemma derivAtTop_congr_nonneg (h : ∀ x, 0 ≤ x → f x = g x) : derivAtTop f = derivAtTop g := by
  refine derivAtTop_congr ?_
  rw [Filter.EventuallyEq, eventually_atTop]
  exact ⟨0, h⟩

lemma derivAtTop_eq_limsup_extendBotLtOne :
    derivAtTop f = limsup (fun x ↦ if 1 ≤ x then (rightDeriv f x : EReal) else ⊥) atTop := by
  refine limsup_congr ?_
  filter_upwards [ite_bot_ae_eq_atTop (fun x ↦ (rightDeriv f x : EReal))] with x hx
  rw [hx]

lemma tendsto_extendBotLtOne_rightDeriv_iff {y : EReal} :
    Tendsto (fun x ↦ if 1 ≤ x then (rightDeriv f x : EReal) else ⊥) atTop (𝓝 y)
      ↔ Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 y) := by
  refine tendsto_congr' ?_
  filter_upwards [ite_bot_ae_eq_atTop (fun x ↦ (rightDeriv f x : EReal))] with x hx
  rw [hx]

lemma derivAtTop_of_tendsto {y : EReal}
    (h : Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 y)) :
    derivAtTop f = y := h.limsup_eq

lemma derivAtTop_of_tendsto_nhds {y : ℝ} (h : Tendsto (rightDeriv f) atTop (𝓝 y)) :
    derivAtTop f = y :=
  derivAtTop_of_tendsto ((continuous_coe_real_ereal.tendsto _).comp h)

lemma derivAtTop_of_tendsto_atTop (h : Tendsto (rightDeriv f) atTop atTop) :
    derivAtTop f = ⊤ := by
  refine derivAtTop_of_tendsto ?_
  rw [EReal.tendsto_nhds_top_iff_real]
  simp only [EReal.coe_lt_coe_iff, eventually_atTop, ge_iff_le]
  rw [tendsto_atTop_atTop] at h
  intro x
  obtain ⟨a, ha⟩ := h (x + 1)
  exact ⟨a, fun b hab ↦ (lt_add_one _).trans_le (ha b hab)⟩

@[simp]
lemma derivAtTop_zero : derivAtTop 0 = 0 := by
  refine derivAtTop_of_tendsto_nhds ?_
  simp only [rightDeriv_zero]
  exact tendsto_const_nhds

@[simp]
lemma derivAtTop_const (c : ℝ) : derivAtTop (fun _ ↦ c) = 0 := by
  refine derivAtTop_of_tendsto_nhds ?_
  simp only [rightDeriv_const]
  exact tendsto_const_nhds

@[simp] lemma derivAtTop_id : derivAtTop id = 1 := derivAtTop_of_tendsto_nhds (by simp)

@[simp] lemma derivAtTop_id' : derivAtTop (fun x ↦ x) = 1 := derivAtTop_id

lemma MonotoneOn.tendsto_derivAtTop (hf : MonotoneOn (rightDeriv f) (Ioi 0)) :
    Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 (derivAtTop f)) := by
  have hf_coe : MonotoneOn (fun x ↦ (rightDeriv f x : EReal)) (Ici 1) :=
    Real.monotone_toEReal.comp_monotoneOn (hf.mono (Ici_subset_Ioi.mpr zero_lt_one))
  obtain ⟨z, hz⟩ : ∃ z, Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 z) :=
    EReal.tendsto_of_monotoneOn hf_coe
  rwa [derivAtTop_of_tendsto hz]

lemma ConvexOn.tendsto_derivAtTop (hf : ConvexOn ℝ (Ici 0) f) :
    Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 (derivAtTop f)) :=
  hf.rightDeriv_mono'.tendsto_derivAtTop

lemma MonotoneOn.derivAtTop_eq_iff {y : EReal} (hf : MonotoneOn (rightDeriv f) (Ioi 0)) :
    derivAtTop f = y ↔ Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 y) := by
  refine ⟨fun h ↦ ?_, fun h ↦ derivAtTop_of_tendsto h⟩
  have h_tendsto := hf.tendsto_derivAtTop
  rwa [h] at h_tendsto

lemma ConvexOn.derivAtTop_eq_iff {y : EReal} (hf : ConvexOn ℝ (Ici 0) f) :
    derivAtTop f = y ↔ Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 y) :=
  hf.rightDeriv_mono'.derivAtTop_eq_iff

lemma MonotoneOn.derivAtTop_eq_top_iff (hf : MonotoneOn (rightDeriv f) (Ioi 0)) :
    derivAtTop f = ⊤ ↔ Tendsto (rightDeriv f) atTop atTop := by
  refine ⟨fun h ↦ ?_, fun h ↦ derivAtTop_of_tendsto_atTop h⟩
  exact EReal.tendsto_toReal_atTop.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (h ▸ hf.tendsto_derivAtTop) (.of_forall fun _ ↦ EReal.coe_ne_top _))

lemma ConvexOn.derivAtTop_eq_top_iff (hf : ConvexOn ℝ (Ici 0) f) :
    derivAtTop f = ⊤ ↔ Tendsto (rightDeriv f) atTop atTop :=
  hf.rightDeriv_mono'.derivAtTop_eq_top_iff

lemma MonotoneOn.derivAtTop_ne_bot (hf : MonotoneOn (rightDeriv f) (Ioi 0)) : derivAtTop f ≠ ⊥ := by
  intro h_eq
  rw [hf.derivAtTop_eq_iff, ← tendsto_extendBotLtOne_rightDeriv_iff] at h_eq
  have h_le := hf.monotone_ite_bot.ge_of_tendsto h_eq 1
  simp at h_le

lemma ConvexOn.derivAtTop_ne_bot (hf : ConvexOn ℝ (Ici 0) f) : derivAtTop f ≠ ⊥ :=
  hf.rightDeriv_mono'.derivAtTop_ne_bot

lemma MonotoneOn.tendsto_toReal_derivAtTop (hf : MonotoneOn (rightDeriv f) (Ioi 0))
    (h_top : derivAtTop f ≠ ⊤) :
    Tendsto (rightDeriv f) atTop (𝓝 (derivAtTop f).toReal) := by
  have h_tendsto : Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 (derivAtTop f)) :=
    hf.tendsto_derivAtTop
  have h_toReal : rightDeriv f = fun x ↦ (rightDeriv f x : EReal).toReal := by ext; simp
  rw [h_toReal]
  exact (EReal.tendsto_toReal h_top hf.derivAtTop_ne_bot).comp h_tendsto

lemma ConvexOn.tendsto_toReal_derivAtTop (hf : ConvexOn ℝ (Ici 0) f) (h_top : derivAtTop f ≠ ⊤) :
    Tendsto (rightDeriv f) atTop (𝓝 (derivAtTop f).toReal) :=
  hf.rightDeriv_mono'.tendsto_toReal_derivAtTop h_top

lemma derivAtTop_add' (hf_cvx : ConvexOn ℝ (Ici 0) f) (hg_cvx : ConvexOn ℝ (Ici 0) g) :
    derivAtTop (f + g) = derivAtTop f + derivAtTop g := by
  rw [(hf_cvx.add hg_cvx).derivAtTop_eq_iff]
  suffices Tendsto (fun x ↦ (rightDeriv f x : EReal) + ↑(rightDeriv g x)) atTop
      (𝓝 (derivAtTop f + derivAtTop g)) by
    refine (tendsto_congr' ?_).mp this
    rw [EventuallyEq, eventually_atTop]
    refine ⟨1, fun x hx ↦ ?_⟩
    change _ = ↑(rightDeriv (fun x ↦ f x + g x) x)
    rw [rightDeriv_add_apply' (hf_cvx.differentiableWithinAt_Ioi' (zero_lt_one.trans_le hx))
        (hg_cvx.differentiableWithinAt_Ioi' (zero_lt_one.trans_le hx))]
    simp only [EReal.coe_add]
  have h_cont : ContinuousAt (fun p : (EReal × EReal) ↦ p.1 + p.2) (derivAtTop f, derivAtTop g) :=
    EReal.continuousAt_add (p := (derivAtTop f, derivAtTop g)) (Or.inr hg_cvx.derivAtTop_ne_bot)
      (Or.inl hf_cvx.derivAtTop_ne_bot)
  change Tendsto ((fun p : (EReal × EReal) ↦ p.1 + p.2)
      ∘ (fun x ↦ (↑(rightDeriv f x), ↑(rightDeriv g x))))
    atTop (𝓝 (derivAtTop f + derivAtTop g))
  exact h_cont.tendsto.comp (hf_cvx.tendsto_derivAtTop.prod_mk_nhds hg_cvx.tendsto_derivAtTop)

lemma derivAtTop_add (hf_cvx : ConvexOn ℝ (Ici 0) f) (hg_cvx : ConvexOn ℝ (Ici 0) g) :
    derivAtTop (fun x ↦ f x + g x) = derivAtTop f + derivAtTop g := derivAtTop_add' hf_cvx hg_cvx

lemma derivAtTop_add_const (hf_cvx : ConvexOn ℝ (Ici 0) f) (c : ℝ) :
    derivAtTop (fun x ↦ f x + c) = derivAtTop f :=
  (derivAtTop_add' hf_cvx (convexOn_const _ (convex_Ici 0))).trans (by simp)

lemma derivAtTop_const_add (hf_cvx : ConvexOn ℝ (Ici 0) f) (c : ℝ) :
    derivAtTop (fun x ↦ c + f x) = derivAtTop f :=
  (derivAtTop_add' (convexOn_const _ (convex_Ici 0)) hf_cvx).trans (by simp)

lemma derivAtTop_sub_const (hf_cvx : ConvexOn ℝ (Ici 0) f) (c : ℝ) :
    derivAtTop (fun x ↦ f x - c) = derivAtTop f := by
  simp_rw [sub_eq_add_neg]
  exact derivAtTop_add_const hf_cvx _

lemma derivAtTop_const_mul (hf_cvx : ConvexOn ℝ (Ici 0) f) {c : ℝ} (hc : c ≠ 0) :
    derivAtTop (fun x ↦ c * f x) = c * derivAtTop f := by
  refine derivAtTop_of_tendsto ?_
  simp only [rightDeriv_const_mul, EReal.coe_mul]
  have h_cont : ContinuousAt (fun p : (EReal × EReal) ↦ p.1 * p.2) (↑c, derivAtTop f) :=
    EReal.continuousAt_mul (p := (c, derivAtTop f)) (Or.inr hf_cvx.derivAtTop_ne_bot)
      (Or.inl ?_) (Or.inl (by simp)) (Or.inl (by simp))
  swap; · simp only [ne_eq, EReal.coe_eq_zero]; exact hc
  change Tendsto ((fun p : (EReal × EReal) ↦ p.1 * p.2) ∘ (fun x ↦ (↑c, ↑(rightDeriv f x))))
    atTop (𝓝 (↑c * derivAtTop f))
  exact h_cont.tendsto.comp (tendsto_const_nhds.prod_mk_nhds hf_cvx.tendsto_derivAtTop)

lemma slope_le_rightDeriv (h_cvx : ConvexOn ℝ (Ici 0) f) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    (f y - f x) / (y - x) ≤ rightDeriv f y := by
  rw [h_cvx.rightDeriv_eq_sInf_slope' (hx.trans_lt hxy)]
  refine le_csInf nonempty_of_nonempty_subtype (fun b hb ↦ ?_)
  obtain ⟨z, hyz, rfl⟩ := hb
  simp only [mem_Ioi] at hyz
  rw [← slope_def_field, slope_comm]
  refine h_cvx.slope_mono (hx.trans hxy.le) ?_ ?_ (hxy.trans hyz).le
  · simp only [mem_diff, mem_Ici, mem_singleton_iff]
    exact ⟨hx, hxy.ne⟩
  · simp only [mem_diff, mem_Ici, mem_singleton_iff]
    exact ⟨(hx.trans hxy.le).trans hyz.le, hyz.ne'⟩

lemma rightDeriv_le_toReal_derivAtTop (h_cvx : ConvexOn ℝ (Ici 0) f) (h : derivAtTop f ≠ ⊤)
    (hx : 0 < x) :
    rightDeriv f x ≤ (derivAtTop f).toReal := by
  have h_tendsto := h_cvx.tendsto_toReal_derivAtTop h
  refine ge_of_tendsto h_tendsto ?_
  rw [eventually_atTop]
  refine ⟨max 1 x, fun y hy ↦ h_cvx.rightDeriv_mono' hx ?_ ?_⟩
  · exact mem_Ioi.mpr (hx.trans_le ((le_max_right _ _).trans hy))
  · exact (le_max_right _ _).trans hy

lemma rightDeriv_le_derivAtTop (h_cvx : ConvexOn ℝ (Ici 0) f) (hx : 0 < x) :
    rightDeriv f x ≤ derivAtTop f := by
  by_cases h : derivAtTop f = ⊤
  · exact h ▸ le_top
  · rw [← EReal.coe_toReal h h_cvx.derivAtTop_ne_bot, EReal.coe_le_coe_iff]
    exact rightDeriv_le_toReal_derivAtTop h_cvx h hx

lemma slope_le_derivAtTop (h_cvx : ConvexOn ℝ (Ici 0) f)
    (h : derivAtTop f ≠ ⊤) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    (f y - f x) / (y - x) ≤ (derivAtTop f).toReal :=
  (slope_le_rightDeriv h_cvx hx hxy).trans
    (rightDeriv_le_toReal_derivAtTop h_cvx h (hx.trans_lt hxy))

lemma le_add_derivAtTop (h_cvx : ConvexOn ℝ (Ici 0) f)
    (h : derivAtTop f ≠ ⊤) {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    f x ≤ f y + (derivAtTop f).toReal * (x - y) := by
  cases eq_or_lt_of_le hyx with
  | inl h_eq => simp [h_eq]
  | inr h_lt =>
    have h_le := slope_le_derivAtTop h_cvx h hy h_lt
    rwa [div_le_iff₀, sub_le_iff_le_add'] at h_le
    simp [h_lt]

lemma le_add_derivAtTop'' (h_cvx : ConvexOn ℝ (Ici 0) f)
    (h : derivAtTop f ≠ ⊤) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f (x + y) ≤ f x + (derivAtTop f).toReal * y := by
  have h_le := le_add_derivAtTop h_cvx h hx (x := x + y) ?_
  · simpa using h_le
  · linarith

lemma le_add_derivAtTop' (h_cvx : ConvexOn ℝ (Ici 0) f)
    (h : derivAtTop f ≠ ⊤) {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    f x ≤ f (x * u) + (derivAtTop f).toReal * x * (1 - u) := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have h := le_add_derivAtTop h_cvx h (mul_nonneg hx hu) (x := x) ?_
  swap;
  · rwa [mul_le_iff_le_one_right]
    exact hx.lt_of_ne' hx0
  rwa [mul_assoc, mul_sub, mul_one]

lemma toReal_le_add_derivAtTop (hf_cvx : ConvexOn ℝ (Ici 0) f) {a b : ENNReal}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    f ((a + b).toReal) ≤ f a.toReal + derivAtTop f * b := by
  by_cases hf_top : derivAtTop f = ⊤
  · rw [hf_top]
    by_cases hb_zero : b = 0
    · simp [hb_zero]
    · rw [EReal.top_mul_ennreal_coe hb_zero, EReal.coe_add_top]
      exact le_top
  · have h_le : a.toReal ≤ (a + b).toReal := by
      gcongr
      · simp [ha, hb]
      · simp
    have h := le_add_derivAtTop hf_cvx hf_top (ENNReal.toReal_nonneg : 0 ≤ a.toReal) h_le
    lift derivAtTop f to ℝ using ⟨hf_top, hf_cvx.derivAtTop_ne_bot⟩ with df
    rw [← EReal.coe_ennreal_toReal hb]
    norm_cast
    refine h.trans_eq ?_
    congr
    rw [sub_eq_iff_eq_add, ← ENNReal.toReal_add hb ha, add_comm]

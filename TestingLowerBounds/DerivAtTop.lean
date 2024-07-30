/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Convex
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import TestingLowerBounds.ForMathlib.EReal

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

lemma Real.monotone_toEReal : Monotone toEReal := Monotone.of_map_inf fun _ ↦ congrFun rfl

lemma Filter.EventuallyEq.derivWithin_eq_nhds {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f₁ f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}
    (h : f₁ =ᶠ[𝓝 x] f) :
    derivWithin f₁ s x = derivWithin f s x := by
  simp_rw [derivWithin]
  rw [Filter.EventuallyEq.fderivWithin_eq_nhds h]

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {f g : ℝ → ℝ} {x : ℝ}

lemma Filter.EventuallyEq.rightDeriv_eq_nhds {x : ℝ} (h : f =ᶠ[𝓝 x] g) :
    rightDeriv f x = rightDeriv g x := h.derivWithin_eq_nhds

section ExtendLinearNeg

noncomputable
def extendLinearNeg (f : ℝ → ℝ) (x : ℝ) : ℝ := if 0 ≤ x then f x else f 0 + (rightDeriv f 0) * x

lemma extendLinearNeg_of_nonneg (hx : 0 ≤ x) : extendLinearNeg f x = f x := if_pos hx

lemma extendLinearNeg_of_neg (hx : x < 0) : extendLinearNeg f x = f 0 + (rightDeriv f 0) * x :=
  if_neg (not_le.mpr hx)

lemma extendLinearNeg_eq_atTop (f : ℝ → ℝ) : extendLinearNeg f =ᶠ[atTop] f := by
  rw [Filter.EventuallyEq, eventually_atTop]
  exact ⟨0, fun _ ↦ extendLinearNeg_of_nonneg⟩

lemma ConvexOn.extendLinearNeg (hf : ConvexOn ℝ (Ici 0) f) :
    ConvexOn ℝ univ (extendLinearNeg f) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  sorry

end ExtendLinearNeg

noncomputable
def derivAtTop (f : ℝ → ℝ) : EReal := limsup (fun x ↦ (rightDeriv f x : EReal)) atTop

lemma rightDeriv_congr_atTop (h : f =ᶠ[atTop] g) :
    rightDeriv f =ᶠ[atTop] rightDeriv g := by
  have h' : ∀ᶠ x in atTop, f =ᶠ[𝓝 x] g := by
    -- todo: replace by clean filter proof?
    simp only [Filter.EventuallyEq, eventually_atTop, ge_iff_le] at h ⊢
    obtain ⟨a, ha⟩ := h
    refine ⟨a + 1, fun b hab ↦ ?_⟩
    have h_ge : ∀ᶠ x in 𝓝 b, a ≤ x := eventually_ge_nhds ((lt_add_one _).trans_le hab)
    filter_upwards [h_ge] using ha
  filter_upwards [h'] with a ha using ha.rightDeriv_eq_nhds

lemma derivAtTop_congr (h : f =ᶠ[atTop] g) : derivAtTop f = derivAtTop g := by
  simp_rw [derivAtTop]
  refine limsup_congr ?_
  filter_upwards [rightDeriv_congr_atTop h] with x hx
  rw [hx]

lemma derivAtTop_congr_nonneg (h : ∀ x, 0 ≤ x → f x = g x) : derivAtTop f = derivAtTop g := by
  refine derivAtTop_congr ?_
  rw [Filter.EventuallyEq, eventually_atTop]
  exact ⟨0, h⟩

@[simp]
lemma derivAtTop_extendLinearNeg : derivAtTop (extendLinearNeg f) = derivAtTop f :=
  derivAtTop_congr_nonneg fun x hx ↦ by simp [extendLinearNeg, hx]

lemma tendsto_rightDeriv_extendLinearNeg_iff {y : EReal} :
    Tendsto (fun x ↦ (rightDeriv (extendLinearNeg f) x : EReal)) atTop (𝓝 y)
      ↔ Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 y) := by
  refine tendsto_congr' ?_
  filter_upwards [rightDeriv_congr_atTop (extendLinearNeg_eq_atTop f)] with x hx
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
lemma derivAtTop_const (c : ℝ) : derivAtTop (fun _ ↦ c) = 0 := by
  refine derivAtTop_of_tendsto_nhds ?_
  simp only [rightDeriv_const]
  exact tendsto_const_nhds

@[simp] lemma derivAtTop_id : derivAtTop id = 1 := derivAtTop_of_tendsto_nhds (by simp)

@[simp] lemma derivAtTop_id' : derivAtTop (fun x ↦ x) = 1 := derivAtTop_id

lemma Monotone.tendsto_derivAtTop (hf : Monotone (rightDeriv f)) :
    Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 (derivAtTop f)) := by
  have hf_coe : Monotone (fun x ↦ (rightDeriv f x : EReal)) := Real.monotone_toEReal.comp hf
  obtain ⟨z, hz⟩ : ∃ z, Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 z) :=
    EReal.tendsto_of_monotone hf_coe
  rwa [derivAtTop_of_tendsto hz]

lemma ConvexOn.tendsto_derivAtTop (hf : ConvexOn ℝ (Ici 0) f) :
    Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 (derivAtTop f)) := by
  rw [← tendsto_rightDeriv_extendLinearNeg_iff, ← derivAtTop_extendLinearNeg]
  exact hf.extendLinearNeg.rightDeriv_mono.tendsto_derivAtTop

lemma Monotone.derivAtTop_eq_iff {y : EReal} (hf : Monotone (rightDeriv f)) :
    derivAtTop f = y ↔ Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 y) := by
  refine ⟨fun h ↦ ?_, fun h ↦ derivAtTop_of_tendsto h⟩
  have h_tendsto := hf.tendsto_derivAtTop
  rwa [h] at h_tendsto

lemma ConvexOn.derivAtTop_eq_iff {y : EReal} (hf : ConvexOn ℝ (Ici 0) f) :
    derivAtTop f = y ↔ Tendsto (fun x ↦ (rightDeriv f x : EReal)) atTop (𝓝 y) := by
  rw [← tendsto_rightDeriv_extendLinearNeg_iff, ← derivAtTop_extendLinearNeg]
  exact hf.extendLinearNeg.rightDeriv_mono.derivAtTop_eq_iff

lemma Monotone.derivAtTop_ne_bot (hf : Monotone (rightDeriv f)) : derivAtTop f ≠ ⊥ := by
  intro h_eq
  rw [hf.derivAtTop_eq_iff] at h_eq
  have h_le := Monotone.ge_of_tendsto (Real.monotone_toEReal.comp hf) h_eq
  simp only [Function.comp_apply, le_bot_iff, EReal.coe_ne_bot, forall_const] at h_le

lemma ConvexOn.derivAtTop_ne_bot (hf : ConvexOn ℝ (Ici 0) f) : derivAtTop f ≠ ⊥ := by
  rw [← derivAtTop_extendLinearNeg]
  exact hf.extendLinearNeg.rightDeriv_mono.derivAtTop_ne_bot

lemma tendsto_slope_derivAtTop (hf_cvx : ConvexOn ℝ (Ici 0) f) (h : derivAtTop f ≠ ⊤) (y : ℝ) :
    Tendsto (fun x ↦ (f x - f y) / (x - y)) atTop (𝓝 (derivAtTop f).toReal) := by
  sorry

lemma toReal_derivAtTop_eq_limsup_slope (hf_cvx : ConvexOn ℝ (Ici 0) f) (h : derivAtTop f ≠ ⊤)
    (y : ℝ) :
    (derivAtTop f).toReal = limsup (fun x ↦ (f x - f y) / (x - y)) atTop := by
  rw [(tendsto_slope_derivAtTop hf_cvx h y).limsup_eq]

lemma derivAtTop_eq_limsup_slope (hf_cvx : ConvexOn ℝ (Ici 0) f) (h : derivAtTop f ≠ ⊤)
    (y : ℝ) :
    derivAtTop f = limsup (fun x ↦ (f x - f y) / (x - y)) atTop := by
  rw [← toReal_derivAtTop_eq_limsup_slope hf_cvx h y, EReal.coe_toReal h hf_cvx.derivAtTop_ne_bot]

lemma derivAtTop_add' (hf_cvx : ConvexOn ℝ (Ici 0) f) (hg_cvx : ConvexOn ℝ (Ici 0) g) :
    derivAtTop (f + g) = derivAtTop f + derivAtTop g := by
  rw [(hf_cvx.add hg_cvx).derivAtTop_eq_iff]
  suffices Tendsto (fun x ↦ (rightDeriv f x : EReal) + ↑(rightDeriv g x)) atTop
      (𝓝 (derivAtTop f + derivAtTop g)) by
    refine (tendsto_congr' ?_).mp this
    rw [EventuallyEq, eventually_atTop]
    refine ⟨1, fun x hx ↦ ?_⟩
    change _ = ↑(rightDeriv (fun x ↦ f x + g x) x)
    rw [rightDeriv_add (hf_cvx.differentiableWithinAt_Ioi' (zero_lt_one.trans_le hx))
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

lemma slope_le_derivAtTop (h_cvx : ConvexOn ℝ (Ici 0) f)
    (h : derivAtTop f ≠ ⊤) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
  (f y - f x) / (y - x) ≤ (derivAtTop f).toReal := by
  sorry

lemma le_add_derivAtTop (h_cvx : ConvexOn ℝ (Ici 0) f)
    (h : derivAtTop f ≠ ⊤) {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    f x ≤ f y + (derivAtTop f).toReal * (x - y) := by
  cases eq_or_lt_of_le hyx with
  | inl h_eq => simp [h_eq]
  | inr h_lt =>
    have h_le := slope_le_derivAtTop h_cvx h hy h_lt
    rwa [div_le_iff, sub_le_iff_le_add'] at h_le
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

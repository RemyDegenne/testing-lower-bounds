/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Convex

/-!

# DerivAtTop

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open Real MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {f g : ℝ → ℝ}

-- we put the coe outside the limsup to ensure it's not ⊥
open Classical in
noncomputable
def derivAtTop (f : ℝ → ℝ) : EReal :=
  if Tendsto (fun x ↦ f x / x) atTop atTop then ⊤ else ↑(limsup (fun x ↦ f x / x) atTop)

lemma bot_lt_derivAtTop : ⊥ < derivAtTop f := by
  rw [derivAtTop]
  split_ifs with h <;> simp

lemma derivAtTop_ne_bot : derivAtTop f ≠ ⊥ := bot_lt_derivAtTop.ne'

lemma derivAtTop_eq_top_iff : derivAtTop f = ⊤ ↔ Tendsto (fun x ↦ f x / x) atTop atTop := by
  rw [derivAtTop]
  split_ifs with h <;> simp [h]

lemma derivAtTop_of_tendsto {y : ℝ} (h : Tendsto (fun x ↦ f x / x) atTop (𝓝 y)) :
    derivAtTop f = y := by
  rw [derivAtTop, if_neg]
  · rw [h.limsup_eq]
  · exact h.not_tendsto (disjoint_nhds_atTop _)

@[simp]
lemma derivAtTop_const (c : ℝ) : derivAtTop (fun _ ↦ c) = 0 := by
  refine derivAtTop_of_tendsto (Tendsto.div_atTop (tendsto_const_nhds) tendsto_id)

@[simp]
lemma derivAtTop_id : derivAtTop id = 1 := by
  refine derivAtTop_of_tendsto ?_
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  simp only [EventuallyEq, id_eq, eventually_atTop, ge_iff_le]
  refine ⟨1, fun x hx ↦ (div_self ?_).symm⟩
  linarith

@[simp]
lemma derivAtTop_id' : derivAtTop (fun x ↦ x) = 1 := derivAtTop_id

lemma tendsto_derivAtTop (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (h : derivAtTop f ≠ ⊤) :
    Tendsto (fun x ↦ f x / x) atTop (𝓝 (derivAtTop f).toReal) := by
  rw [ne_eq, derivAtTop_eq_top_iff] at h
  obtain ⟨l, h'⟩ : ∃ l, Tendsto (fun x ↦ f x / x) atTop (𝓝 l) :=
      hf_cvx.slope_tendsto_atTop.resolve_left h
  rw [derivAtTop, if_neg h, h'.limsup_eq, EReal.toReal_coe]
  exact h'

lemma tendsto_slope_derivAtTop (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (h : derivAtTop f ≠ ⊤) (y : ℝ) :
    Tendsto (fun x ↦ (f x - f y) / (x - y)) atTop (𝓝 (derivAtTop f).toReal) := by
  sorry

lemma toReal_derivAtTop_eq_limsup_slope (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (h : derivAtTop f ≠ ⊤)
    (y : ℝ) :
    (derivAtTop f).toReal = limsup (fun x ↦ (f x - f y) / (x - y)) atTop := by
  rw [(tendsto_slope_derivAtTop hf_cvx h y).limsup_eq]

lemma derivAtTop_eq_limsup_slope (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (h : derivAtTop f ≠ ⊤)
    (y : ℝ) :
    derivAtTop f = limsup (fun x ↦ (f x - f y) / (x - y)) atTop := by
  rw [← toReal_derivAtTop_eq_limsup_slope hf_cvx h y, EReal.coe_toReal h derivAtTop_ne_bot]

lemma derivAtTop_add (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hg_cvx : ConvexOn ℝ (Set.Ici 0) g) :
    derivAtTop (fun x ↦ f x + g x) = derivAtTop f + derivAtTop g := by
  by_cases hf :derivAtTop f = ⊤
  · rw [hf, EReal.top_add_of_ne_bot derivAtTop_ne_bot, derivAtTop_eq_top_iff]
    simp_rw [add_div]
    by_cases hg : derivAtTop g = ⊤
    · rw [derivAtTop_eq_top_iff] at hg
      exact tendsto_atTop_add (derivAtTop_eq_top_iff.mp hf) hg
    · exact Tendsto.atTop_add (derivAtTop_eq_top_iff.mp hf) (tendsto_derivAtTop hg_cvx hg)
  · by_cases hg : derivAtTop g = ⊤
    · rw [hg, EReal.add_top_of_ne_bot derivAtTop_ne_bot, derivAtTop_eq_top_iff]
      simp_rw [add_div]
      exact Tendsto.add_atTop (tendsto_derivAtTop hf_cvx hf) (derivAtTop_eq_top_iff.mp hg)
    · have hf' := tendsto_derivAtTop hf_cvx hf
      have hg' := tendsto_derivAtTop hg_cvx hg
      lift derivAtTop f to ℝ using ⟨hf, derivAtTop_ne_bot⟩ with df
      lift derivAtTop g to ℝ using ⟨hg, derivAtTop_ne_bot⟩ with dg
      refine derivAtTop_of_tendsto ?_
      simp_rw [add_div]
      exact hf'.add hg'

lemma derivAtTop_add' (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hg_cvx : ConvexOn ℝ (Set.Ici 0) g) :
    derivAtTop (f + g) = derivAtTop f + derivAtTop g := by
  rw [← derivAtTop_add hf_cvx hg_cvx]
  rfl

lemma derivAtTop_add_const (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (c : ℝ) :
    derivAtTop (fun x ↦ f x + c) = derivAtTop f := by
  by_cases hf : derivAtTop f = ⊤
  · rw [hf, derivAtTop_eq_top_iff]
    simp_rw [add_div]
    refine Tendsto.atTop_add (derivAtTop_eq_top_iff.mp hf) (C := 0) ?_
    exact Tendsto.div_atTop tendsto_const_nhds tendsto_id
  · have h_tendsto := tendsto_derivAtTop hf_cvx hf
    lift derivAtTop f to ℝ using ⟨hf, derivAtTop_ne_bot⟩ with df
    refine derivAtTop_of_tendsto ?_
    simp_rw [add_div]
    rw [← add_zero df]
    exact h_tendsto.add (Tendsto.div_atTop tendsto_const_nhds tendsto_id)

lemma derivAtTop_sub_const (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (c : ℝ) :
    derivAtTop (fun x ↦ f x - c) = derivAtTop f := by
  simp_rw [sub_eq_add_neg]
  exact derivAtTop_add_const hf_cvx _

lemma derivAtTop_const_mul (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) {c : ℝ} (hc : 0 < c) :
    derivAtTop (fun x ↦ c * f x) = c * derivAtTop f := by
  by_cases h : Tendsto (fun x ↦ f x / x) atTop atTop
  · rw [derivAtTop_eq_top_iff.mpr h, derivAtTop_eq_top_iff.mpr, EReal.mul_top_of_pos]
    · exact mod_cast hc
    · simp_rw [mul_div_assoc]
      exact Tendsto.const_mul_atTop hc h
  · have h_top : derivAtTop f ≠ ⊤ := by
      refine fun h_eq ↦ h ?_
      rwa [← derivAtTop_eq_top_iff]
    have : derivAtTop f = ↑(derivAtTop f).toReal := by
      rw [EReal.coe_toReal h_top derivAtTop_ne_bot]
    rw [this, ← EReal.coe_mul]
    refine derivAtTop_of_tendsto ?_
    simp_rw [mul_div_assoc]
    exact (tendsto_derivAtTop hf_cvx h_top).const_mul _

lemma derivAtTop_const_mul_of_ne_top (hf_cvx : ConvexOn ℝ (Set.Ici 0) f)
    (h_deriv : derivAtTop f ≠ ⊤) (c : ℝ) :
    derivAtTop (fun x ↦ c * f x) = c * derivAtTop f := by
  have h_tendsto := tendsto_derivAtTop hf_cvx h_deriv
  lift derivAtTop f to ℝ using ⟨h_deriv, derivAtTop_ne_bot⟩ with df
  rw [← EReal.coe_mul]
  refine derivAtTop_of_tendsto ?_
  simp_rw [mul_div_assoc]
  exact h_tendsto.const_mul c

lemma slope_le_derivAtTop (h_cvx : ConvexOn ℝ (Set.Ici 0) f)
    (h : derivAtTop f ≠ ⊤) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
  (f y - f x) / (y - x) ≤ (derivAtTop f).toReal := by
  refine Monotone.ge_of_tendsto (f := fun y ↦ (f y - f x) / (y - x)) ?_ ?_ y
  · have h_mono : ∀ z, y < z → (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
      fun z hyz ↦ ConvexOn.slope_mono_adjacent h_cvx hx (hx.trans (hxy.trans hyz).le) hxy hyz
    sorry -- not true. Need to restrict to (x, ∞)
  · exact tendsto_slope_derivAtTop h_cvx h x

lemma le_add_derivAtTop (h_cvx : ConvexOn ℝ (Set.Ici 0) f)
    (h : derivAtTop f ≠ ⊤) {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    f x ≤ f y + (derivAtTop f).toReal * (x - y) := by
  cases eq_or_lt_of_le hyx with
  | inl h_eq => simp [h_eq]
  | inr h_lt =>
    have h_le := slope_le_derivAtTop h_cvx h hy h_lt
    rwa [div_le_iff, sub_le_iff_le_add'] at h_le
    simp [h_lt]

lemma le_add_derivAtTop'' (h_cvx : ConvexOn ℝ (Set.Ici 0) f)
    (h : derivAtTop f ≠ ⊤) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f (x + y) ≤ f x + (derivAtTop f).toReal * y := by
  have h_le := le_add_derivAtTop h_cvx h hx (x := x + y) ?_
  · simpa using h_le
  · linarith

lemma le_add_derivAtTop' (h_cvx : ConvexOn ℝ (Set.Ici 0) f)
    (h : derivAtTop f ≠ ⊤) {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    f x ≤ f (x * u) + (derivAtTop f).toReal * x * (1 - u) := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have h := le_add_derivAtTop h_cvx h (mul_nonneg hx hu) (x := x) ?_
  swap;
  · rwa [mul_le_iff_le_one_right]
    exact hx.lt_of_ne' hx0
  rwa [mul_assoc, mul_sub, mul_one]

lemma toReal_le_add_derivAtTop (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) {a b : ENNReal}
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
    lift derivAtTop f to ℝ using ⟨hf_top, derivAtTop_ne_bot⟩ with df
    rw [← EReal.coe_ennreal_toReal hb]
    norm_cast
    refine h.trans_eq ?_
    congr
    rw [sub_eq_iff_eq_add, ← ENNReal.toReal_add hb ha, add_comm]

end ProbabilityTheory

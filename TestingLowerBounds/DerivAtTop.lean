/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.ForMathlib.EReal
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.MeanValue

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
  {μ ν : Measure α} {κ η : kernel α β} {f g : ℝ → ℝ}

lemma _root_.ConvexOn.exists_affine_le {s : Set ℝ} (hf : ConvexOn ℝ s f) (hs : Convex ℝ s) :
    ∃ c c', ∀ x ∈ s, c * x + c' ≤ f x := by
  sorry

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

lemma _root_.ConvexOn.slope_tendsto_atTop (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Tendsto (fun x ↦ f x / x) atTop atTop ∨ ∃ l, Tendsto (fun x ↦ f x / x) atTop (𝓝 l) := by
  have h_mono : ∀ x y (hx : 0 < x) (hy : x ≤ y), (f x - f 0) / x ≤ (f y - f 0) / y := by
    intro x y hx_pos hxy_le
    have h := hf_cvx.secant_mono (a := 0) (x := x) (y := y) (by simp) hx_pos.le
      (hx_pos.le.trans hxy_le) hx_pos.ne' (hx_pos.trans_le hxy_le).ne' hxy_le
    simpa using h
  suffices Tendsto (fun x ↦ if x ≤ 1 then (f 1 - f 0) else (f x - f 0) / x) atTop atTop
      ∨ ∃ l, Tendsto (fun x ↦ if x ≤ 1 then (f 1 - f 0) else (f x - f 0) / x) atTop (𝓝 l) by
    sorry
  refine tendsto_of_monotone (fun x y hxy ↦ ?_)
  split_ifs with hx hy hy
  · exact le_rfl
  · simpa using h_mono 1 y zero_lt_one (not_le.mp hy).le
  · exact absurd (hxy.trans hy) hx
  · simpa using h_mono x y (zero_lt_one.trans (not_le.mp hx)) hxy

lemma tendsto_derivAtTop (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (h : derivAtTop f ≠ ⊤) :
    Tendsto (fun x ↦ f x / x) atTop (𝓝 (derivAtTop f).toReal) := by
  rw [ne_eq, derivAtTop_eq_top_iff] at h
  obtain ⟨l, h'⟩ : ∃ l, Tendsto (fun x ↦ f x / x) atTop (𝓝 l) :=
      hf_cvx.slope_tendsto_atTop.resolve_left h
  rw [derivAtTop, if_neg h, h'.limsup_eq, EReal.toReal_coe]
  exact h'

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

lemma le_add_derivAtTop (h_cvx : ConvexOn ℝ (Set.Ici 0) f)
    (h : derivAtTop f ≠ ⊤) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f x ≤ f y + (derivAtTop f).toReal * (x - y) := by
  sorry

lemma le_add_derivAtTop' (h_cvx : ConvexOn ℝ (Set.Ici 0) f)
    (h : derivAtTop f ≠ ⊤) {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) :
    f x ≤ f (x * u) + (derivAtTop f).toReal * x * (1 - u) := by
  refine (le_add_derivAtTop h_cvx h hx (mul_nonneg hx hu)).trans_eq ?_
  rw [mul_assoc, mul_sub, mul_sub, mul_one, mul_sub]

end ProbabilityTheory

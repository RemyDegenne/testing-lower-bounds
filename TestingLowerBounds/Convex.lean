/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.ForMathlib.EReal
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.MeanValue

/-!

# Properties of convex functions

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open Real MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

variable {f g : ℝ → ℝ} {s : Set ℝ} {x : ℝ}

namespace ConvexOn

lemma exists_affine_le (hf : ConvexOn ℝ s f) (hs : Convex ℝ s) :
    ∃ c c', ∀ x ∈ s, c * x + c' ≤ f x := by
  sorry

lemma sSup_affine_eq (hf : ConvexOn ℝ s f) (hs : Convex ℝ s) (hxs : x ∈ s) :
    sSup {z : ℝ | ∃ c c', z = c * x + c' ∧ ∀ y, c * y + c' ≤ f y} = f x := by
  sorry

lemma iSup_affine_eq (hf : ConvexOn ℝ s f) (hs : Convex ℝ s) (hxs : x ∈ s) :
    ⨆ p : {p' : ℝ × ℝ | ∀ y : ℝ, p'.1 * y + p'.2 ≤ f y}, p.1.1 * x + p.1.2 = f x := by
  sorry

lemma slope_tendsto_atTop (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) :
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

lemma comp_neg {𝕜 F β : Type*} [LinearOrderedField 𝕜] [AddCommGroup F]
    [OrderedAddCommMonoid β] [Module 𝕜 F] [SMul 𝕜 β] {f : F → β} {s : Set F}
    (hf : ConvexOn 𝕜 s f) :
    ConvexOn 𝕜 (-s) (fun x ↦ f (-x)) := by
  refine ⟨hf.1.neg, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simp_rw [neg_add_rev, ← smul_neg, add_comm]
  exact hf.2 hx hy ha hb hab

lemma comp_neg_iff {𝕜 F β : Type*} [LinearOrderedField 𝕜] [AddCommGroup F]
    [OrderedAddCommMonoid β] [Module 𝕜 F] [SMul 𝕜 β] {f : F → β} {s : Set F}  :
    ConvexOn 𝕜 (-s) (fun x ↦ f (-x)) ↔ ConvexOn 𝕜 s f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ConvexOn.comp_neg h⟩
  rw [← neg_neg s, ← Function.comp_id f, ← neg_comp_neg, ← Function.comp.assoc]
  exact h.comp_neg

end ConvexOn

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
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

--this can be stated in much greater generality
lemma const_mul_id (c : ℝ) : ConvexOn ℝ .univ (fun (x : ℝ) ↦ c * x) := by
  refine ⟨convex_univ, fun _ _ _ _ _ _ _ _ _ ↦ Eq.le ?_⟩
  simp only [smul_eq_mul]
  ring

end ConvexOn

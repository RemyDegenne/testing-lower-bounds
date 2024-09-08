/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import TestingLowerBounds.ForMathlib.LeftRightDeriv

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
  cases Set.eq_empty_or_nonempty (interior s) with
  | inl h =>
    -- todo: there is at most one point in s
    sorry
  | inr h =>
    obtain ⟨x, hx⟩ := h
    refine ⟨rightDeriv f x, f x - rightDeriv f x * x, fun y hy ↦ ?_⟩
    rw [add_comm]
    cases lt_trichotomy x y with
    | inl hxy =>
      have : rightDeriv f x ≤ slope f x y := rightDeriv_le_slope hf hx hy hxy
      rw [slope_def_field] at this
      rwa [le_div_iff₀ (by simp [hxy]), le_sub_iff_add_le, add_comm, mul_sub, add_sub,
        add_sub_right_comm] at this
    | inr hyx =>
      suffices slope f x y ≤ rightDeriv f x by
        rw [slope_def_field] at this
        sorry
      sorry

end ConvexOn

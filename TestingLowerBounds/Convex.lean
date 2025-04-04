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

-- maybe this could be called `affine_rightDeriv_le_of_mem_interior` and the next lemma `affine_leftDeriv_le_of_mem_interior`
lemma affine_le_of_mem_interior (hf : ConvexOn ℝ s f) {x y : ℝ} (hx : x ∈ interior s) (hy : y ∈ s) :
    rightDeriv f x * y + (f x - rightDeriv f x * x) ≤ f y := by
  rw [add_comm]
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · have : rightDeriv f x ≤ slope f x y := rightDeriv_le_slope hf hx hy hxy
    rw [slope_def_field] at this
    rwa [le_div_iff₀ (by simp [hxy]), le_sub_iff_add_le, add_comm, mul_sub, add_sub,
      add_sub_right_comm] at this
  · simp [h_eq]
  · have : slope f x y ≤ rightDeriv f x :=
      (slope_le_leftDeriv hf hx hy hyx).trans (leftDeriv_le_rightDeriv_of_mem_interior hf hx)
    rw [slope_def_field] at this
    rw [← neg_div_neg_eq, neg_sub, neg_sub] at this
    rwa [div_le_iff₀ (by simp [hyx]), sub_le_iff_le_add, mul_sub, ← sub_le_iff_le_add',
      sub_sub_eq_add_sub, add_sub_right_comm] at this

lemma affine_le_of_mem_interior' (hf : ConvexOn ℝ s f) {x y : ℝ} (hx : x ∈ interior s) (hy : y ∈ s) :
    leftDeriv f x * y + (f x - leftDeriv f x * x) ≤ f y := by
  rw [add_comm]
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · have : leftDeriv f x ≤ slope f x y :=
      (leftDeriv_le_rightDeriv_of_mem_interior hf hx).trans (rightDeriv_le_slope hf hx hy hxy)
    rwa [slope_def_field, le_div_iff₀ (by simp [hxy]), le_sub_iff_add_le, add_comm, mul_sub,
      add_sub, add_sub_right_comm] at this
  · simp [h_eq]
  · have : slope f x y ≤ leftDeriv f x := slope_le_leftDeriv hf hx hy hyx
    rwa [slope_def_field, ← neg_div_neg_eq, neg_sub, neg_sub, div_le_iff₀ (by simp [hyx]),
      sub_le_iff_le_add, mul_sub, ← sub_le_iff_le_add', sub_sub_eq_add_sub,
      add_sub_right_comm] at this

lemma _root_.Convex.subsingleton_of_interior_eq_empty (hs : Convex ℝ s) (h : interior s = ∅) :
    s.Subsingleton := by
  intro x hx y hy
  by_contra h_ne
  wlog h_lt : x < y
  · refine this hs h hy hx (Ne.symm h_ne) ?_
    exact lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm h_ne)
  · have h_subset : Set.Icc x y ⊆ s := by
      rw [← segment_eq_Icc h_lt.le]
      exact hs.segment_subset hx hy
    have : Set.Ioo x y ⊆ interior s := by
      rw [← interior_Icc]
      exact interior_mono h_subset
    simp only [h, Set.subset_empty_iff, Set.Ioo_eq_empty_iff] at this
    exact this h_lt

lemma exists_affine_le (hf : ConvexOn ℝ s f) (hs : Convex ℝ s) :
    ∃ c c', ∀ x ∈ s, c * x + c' ≤ f x := by
  cases Set.eq_empty_or_nonempty (interior s) with
  | inl h => -- there is at most one point in `s`
    have hs_sub : s.Subsingleton := hs.subsingleton_of_interior_eq_empty h
    cases Set.eq_empty_or_nonempty s with
    | inl h' => simp [h']
    | inr h' => -- there is exactly one point in `s`
      obtain ⟨x, hxs⟩ := h'
      refine ⟨0, f x, fun y hys ↦ ?_⟩
      simp [hs_sub hxs hys]
  | inr h => -- there is a point in the interior of `s`
    obtain ⟨x, hx⟩ := h
    refine ⟨rightDeriv f x, f x - rightDeriv f x * x, fun y hy ↦ ?_⟩
    exact affine_le_of_mem_interior hf hx hy

end ConvexOn

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.KullbackLeibler

/-!
# Rényi divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real MeasureTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

open Classical in
noncomputable def renyiReal (a : ℝ) (μ ν : Measure α) : ℝ :=
  if a = 0 then - log (ν {x | 0 < (∂μ/∂ν) x}).toReal
  else if a = 1 then klReal μ ν
  else if a < 1 ∨ μ ≪ ν
    -- todo: review this def
    then (a - 1)⁻¹ * log (1 + (a - 1) * (fDiv (fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)) μ ν).toReal)
    else 0

lemma renyiReal_zero (μ ν : Measure α) :
    renyiReal 0 μ ν = - log (ν {x | 0 < (∂μ/∂ν) x}).toReal := if_pos rfl

lemma renyiReal_one (μ ν : Measure α) : renyiReal 1 μ ν = klReal μ ν := by
  rw [renyiReal, if_neg (by simp), if_pos rfl]

lemma renyiReal_of_pos_of_lt_one (μ ν : Measure α) (ha_pos : 0 < a) (ha_lt_one : a < 1) :
    renyiReal a μ ν
      = (a - 1)⁻¹ * log (1 + (a - 1) * (fDiv (fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)) μ ν).toReal) := by
  rw [renyiReal, if_neg ha_pos.ne', if_neg ha_lt_one.ne, if_pos (Or.inl ha_lt_one)]

lemma renyiReal_of_one_lt (ha_one_lt : 1 < a) (hμν : μ ≪ ν) :
    renyiReal a μ ν
      = (a - 1)⁻¹ * log (1 + (a - 1) * (fDiv (fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)) μ ν).toReal) := by
  rw [renyiReal, if_neg (zero_lt_one.trans ha_one_lt).ne', if_neg ha_one_lt.ne',
    if_pos (Or.inr hμν)]

lemma renyiReal_of_one_lt_of_not_ac (ha_one_lt : 1 < a) (hμν : ¬ μ ≪ ν) :
    renyiReal a μ ν = 0 := by
  rw [renyiReal, if_neg (zero_lt_one.trans ha_one_lt).ne', if_neg ha_one_lt.ne',
    if_neg]
  push_neg
  exact ⟨ha_one_lt.le, hμν⟩

lemma continuous_renyi_fun (ha_pos : 0 < a) :
    Continuous (fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)) := by
  refine continuous_const.mul (Continuous.sub ?_ continuous_const)
  rw [continuous_iff_continuousAt]
  exact fun _ ↦ continuousAt_rpow_const _ _ (Or.inr ha_pos)

lemma renyi_fun_one_eq_zero : (fun x : ℝ ↦ (a - 1)⁻¹ * (x ^ a - 1)) 1 = 0 := by simp

lemma convexOn_renyi_fun (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) :
    ConvexOn ℝ (Set.Ici 0) (fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)) := by
  cases le_total a 1 with
  | inl ha =>
    have : (fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)) = - (fun x ↦ (1 - a)⁻¹ * (x ^ a - 1)) := by
      ext x
      simp only [Pi.neg_apply]
      rw [← neg_mul, neg_inv, neg_sub]
    rw [this]
    refine ConcaveOn.neg ?_
    have h : ConcaveOn ℝ (Set.Ici 0) fun x : ℝ ↦ x ^ a := by
      sorry
    simp_rw [← smul_eq_mul]
    exact ConcaveOn.smul (by simp [ha]) (h.sub (convexOn_const _ (convex_Ici 0)))
  | inr ha =>
    have h := convexOn_rpow ha
    simp_rw [← smul_eq_mul]
    refine ConvexOn.smul (by simp [ha]) ?_
    exact h.sub (concaveOn_const _ (convex_Ici 0))

end ProbabilityTheory

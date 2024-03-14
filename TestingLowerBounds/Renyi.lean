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
    then (a - 1)⁻¹ * log (1 + (a - 1) * fDivReal (fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)) μ ν)
    else 0

lemma renyiReal_zero (μ ν : Measure α) :
    renyiReal 0 μ ν = - log (ν {x | 0 < (∂μ/∂ν) x}).toReal := if_pos rfl

lemma renyiReal_one (μ ν : Measure α) : renyiReal 1 μ ν = klReal μ ν := by
  rw [renyiReal, if_neg (by simp), if_pos rfl]

lemma renyiReal_of_pos_of_lt_one (μ ν : Measure α) (ha_pos : 0 < a) (ha_lt_one : a < 1) :
    renyiReal a μ ν
      = (a - 1)⁻¹ * log (1 + (a - 1) * fDivReal (fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)) μ ν) := by
  rw [renyiReal, if_neg ha_pos.ne', if_neg ha_lt_one.ne, if_pos (Or.inl ha_lt_one)]

lemma renyiReal_of_one_lt (ha_one_lt : 1 < a) (hμν : μ ≪ ν) :
    renyiReal a μ ν
      = (a - 1)⁻¹ * log (1 + (a - 1) * fDivReal (fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)) μ ν) := by
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
    sorry
  | inr ha =>
    have h := convexOn_rpow ha
    sorry

end ProbabilityTheory

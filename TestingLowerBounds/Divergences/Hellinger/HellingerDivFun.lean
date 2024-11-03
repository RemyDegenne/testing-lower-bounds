/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.Hellinger.HellingerFun

/-!
# Hellinger divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details

-/

open Real MeasureTheory Filter MeasurableSpace Set

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

noncomputable
def hellingerDivFun (a : ℝ) : DivFunction :=
  if ha : a ≤ 0 then 0
  else if a = 1 then klDivFun  -- todo: absorb into the next case?
  else DivFunction.ofReal (hellingerFun a)
    ((convexOn_hellingerFun (not_le.mp ha).le).subset (Ioi_subset_Ici le_rfl) (convex_Ioi _))
    hellingerFun_apply_one_eq_zero rightDeriv_hellingerFun_one

@[simp]
lemma hellingerDivFun_of_nonpos (ha : a ≤ 0) : hellingerDivFun a = 0 := dif_pos ha

lemma hellingerDivFun_zero : hellingerDivFun 0 = 0 := dif_pos le_rfl

@[simp]
lemma hellingerDivFun_one : hellingerDivFun 1 = klDivFun := by
  rw [hellingerDivFun, dif_neg (not_le.mpr zero_lt_one), if_pos rfl]

lemma hellingerDivFun_of_pos_of_ne_one (ha_pos : 0 < a) (ha_one : a ≠ 1) :
    hellingerDivFun a = DivFunction.ofReal (hellingerFun a)
      ((convexOn_hellingerFun ha_pos.le).subset (Ioi_subset_Ici le_rfl) (convex_Ioi _))
      hellingerFun_apply_one_eq_zero rightDeriv_hellingerFun_one := by
  rw [hellingerDivFun, dif_neg (not_le.mpr ha_pos), if_neg ha_one]

lemma hellingerDivFun_apply_zero_of_pos (ha_pos : 0 < a) : hellingerDivFun a 0 = 1 := by
  by_cases ha_one : a = 1
  · simp [ha_one, hellingerFun_one]
  rw [hellingerDivFun_of_pos_of_ne_one ha_pos ha_one,
    DivFunction.ofReal_apply_zero_of_continuousWithinAt]
  · simp
  · exact (continuous_hellingerFun ha_pos).continuousWithinAt

@[simp]
lemma hellingerDivFun_apply_zero :
    hellingerDivFun a 0 = if a ≤ 0 then 0 else 1 := by
  split_ifs with h0
  · simp [h0]
  · exact hellingerDivFun_apply_zero_of_pos (not_le.mp h0)

@[simp]
lemma derivAtTop_hellingerDivFun :
    (hellingerDivFun a).derivAtTop =
      if a ≤ 0 then 0
      else if a < 1 then ENNReal.ofReal (a * (1 - a)⁻¹)
      else ∞ := by
  split_ifs with h h_one
  · simp [h]
  · rw [hellingerDivFun_of_pos_of_ne_one (not_le.mp h) h_one.ne]
    rw [DivFunction.derivAtTop_ofReal]
    refine Tendsto.limsup_eq ?_
    refine ENNReal.tendsto_ofReal ?_
    exact tendsto_rightDeriv_hellingerFun_atTop_of_lt_one h_one
  · by_cases ha_one : a = 1
    · simp [ha_one]
    rw [hellingerDivFun_of_pos_of_ne_one (not_le.mp h) ha_one]
    refine DivFunction.derivAtTop_ofReal_of_tendsto_atTop ?_
    exact tendsto_rightDeriv_hellingerFun_atTop_of_one_lt
      ((not_lt.mp h_one).lt_of_ne (Ne.symm ha_one))

lemma derivAtTop_hellingerDivFun_of_lt_one (ha_pos : 0 < a) (ha_lt : a < 1) :
    (hellingerDivFun a).derivAtTop = ENNReal.ofReal (a * (1 - a)⁻¹) := by
  simp [derivAtTop_hellingerDivFun, not_le.mpr ha_pos, ha_lt]

lemma derivAtTop_hellingerDivFun_of_one_le (ha_le : 1 ≤ a) :
    (hellingerDivFun a).derivAtTop = ∞ := by
  simp [derivAtTop_hellingerDivFun, not_le.mpr (zero_lt_one.trans_le ha_le), ha_le]

lemma derivAtTop_hellingerDivFun_one : (hellingerDivFun 1).derivAtTop = ∞ :=
  derivAtTop_hellingerDivFun_of_one_le le_rfl

@[simp]
lemma derivAtTop_hellingerDivFun_eq_top_iff : (hellingerDivFun a).derivAtTop = ∞ ↔ 1 ≤ a := by
  simp only [derivAtTop_hellingerDivFun]
  split_ifs with h1 h2
  · simp [h1, h1.trans_lt zero_lt_one]
  · simp [h1, h2]
  · simp [h1, h2, not_lt.mp h2]

end ProbabilityTheory

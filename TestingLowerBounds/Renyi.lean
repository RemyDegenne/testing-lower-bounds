/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.KullbackLeibler
import TestingLowerBounds.Hellinger

/-!
# Rényi divergence

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

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

open Classical in
noncomputable def renyiDiv (a : ℝ) (μ ν : Measure α) : EReal :=
  if a = 0 then - log (ν {x | 0 < (∂μ/∂ν) x}).toReal
  else if a = 1 then kl μ ν
  else if hellingerDiv a μ ν ≠ ⊤
    then (a - 1)⁻¹ * log (1 + (a - 1) * (hellingerDiv a μ ν).toReal)
    else ⊤

@[simp]
lemma renyiDiv_zero (μ ν : Measure α) :
    renyiDiv 0 μ ν = - log (ν {x | 0 < (∂μ/∂ν) x}).toReal := if_pos rfl

@[simp]
lemma renyiDiv_one (μ ν : Measure α) : renyiDiv 1 μ ν = kl μ ν := by
  rw [renyiDiv, if_neg (by simp), if_pos rfl]

lemma renyiDiv_eq_top_iff_hellingerDiv_eq_top [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) :
    renyiDiv a μ ν = ⊤ ↔ hellingerDiv a μ ν = ⊤ := by
  simp only [renyiDiv, ha_pos.ne', ↓reduceIte, ha_ne_one, ne_eq, ite_not, ite_eq_left_iff]
  rw [← EReal.coe_mul]
  simp only [EReal.coe_ne_top, imp_false, not_not]

lemma renyiDiv_of_not_integrable [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_pos : 0 < a) (ha_ne_one : a ≠ 1)
    (h_int : ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    renyiDiv a μ ν = ⊤ := by
  rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top ha_pos ha_ne_one]
  cases le_total 1 a with
  | inl ha =>
    rw [hellingerDiv_eq_top_iff_of_one_lt (lt_of_le_of_ne ha (Ne.symm ha_ne_one))]
    exact Or.inl h_int
  | inr ha =>
    rwa [hellingerDiv_eq_top_iff_of_lt_one ha_pos (lt_of_le_of_ne ha ha_ne_one)]

lemma renyiDiv_of_lt_one (μ ν : Measure α) [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_pos : 0 < a) (ha_lt_one : a < 1)
    (h_int : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    renyiDiv a μ ν = (a - 1)⁻¹ * log (1 + (a - 1) * (hellingerDiv a μ ν).toReal) := by
  rw [renyiDiv, if_neg ha_pos.ne', if_neg ha_lt_one.ne,
    if_pos ((hellingerDiv_ne_top_iff_of_lt_one ha_pos ha_lt_one _ _).mpr h_int)]

lemma renyiDiv_of_one_lt_of_ac [IsFiniteMeasure μ] [SigmaFinite ν] (ha_one_lt : 1 < a)
    (h_int : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    renyiDiv a μ ν = (a - 1)⁻¹ * log (1 + (a - 1) * (hellingerDiv a μ ν).toReal) := by
  rw [renyiDiv, if_neg (zero_lt_one.trans ha_one_lt).ne', if_neg ha_one_lt.ne',
    if_pos ((hellingerDiv_ne_top_iff_of_one_lt ha_one_lt _ _).mpr ⟨h_int, hμν⟩)]

lemma renyiDiv_of_one_lt_of_not_ac [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_one_lt : 1 < a) (hμν : ¬ μ ≪ ν) :
    renyiDiv a μ ν = ⊤ := by
  rw [renyiDiv, if_neg (zero_lt_one.trans ha_one_lt).ne', if_neg ha_one_lt.ne', if_neg]
  rw [hellingerDiv_ne_top_iff_of_one_lt ha_one_lt]
  push_neg
  exact fun _ ↦ hμν

end ProbabilityTheory

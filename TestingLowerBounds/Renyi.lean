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

open Real MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

section RenyiFun

noncomputable
def renyiFun (a : ℝ) : ℝ → ℝ := fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)

lemma continuous_renyiFun (ha_pos : 0 < a) :
    Continuous (renyiFun a) := by
  refine continuous_const.mul (Continuous.sub ?_ continuous_const)
  rw [continuous_iff_continuousAt]
  exact fun _ ↦ continuousAt_rpow_const _ _ (Or.inr ha_pos)

lemma renyiFun_one_eq_zero : renyiFun a 1 = 0 := by simp [renyiFun]

lemma convexOn_renyiFun (ha_pos : 0 < a) :
    ConvexOn ℝ (Set.Ici 0) (renyiFun a) := by
  cases le_total a 1 with
  | inl ha =>
    have : renyiFun a = - (fun x ↦ (1 - a)⁻¹ * (x ^ a - 1)) := by
      ext x
      simp only [Pi.neg_apply]
      rw [← neg_mul, neg_inv, neg_sub, renyiFun]
    rw [this]
    refine ConcaveOn.neg ?_
    have h : ConcaveOn ℝ (Set.Ici 0) fun x : ℝ ↦ x ^ a := by
      sorry
    simp_rw [← smul_eq_mul]
    exact ConcaveOn.smul (by simp [ha]) (h.sub (convexOn_const _ (convex_Ici 0)))
  | inr ha =>
    have h := convexOn_rpow ha
    unfold renyiFun
    simp_rw [← smul_eq_mul]
    refine ConvexOn.smul (by simp [ha]) ?_
    exact h.sub (concaveOn_const _ (convex_Ici 0))

lemma tendsto_renyiFun_div_atTop_of_one_lt (ha : 1 < a) :
    Tendsto (fun x ↦ renyiFun a x / x) atTop atTop := by
  sorry

lemma tendsto_renyiFun_div_atTop_of_lt_one (ha_pos : 0 < a) (ha : a < 1) :
    Tendsto (fun x ↦ renyiFun a x / x) atTop (𝓝 0) := by
  sorry

lemma derivAtTop_renyiFun_of_one_lt (ha : 1 < a) : derivAtTop (renyiFun a) = ⊤ := by
  rw [derivAtTop, if_pos]
  exact tendsto_renyiFun_div_atTop_of_one_lt ha

lemma derivAtTop_renyiFun_of_lt_one (ha_pos : 0 < a) (ha : a < 1) :
    derivAtTop (renyiFun a) = 0 :=
  derivAtTop_of_tendsto (tendsto_renyiFun_div_atTop_of_lt_one ha_pos ha)

end RenyiFun

section FDiv

lemma fDiv_renyiFun_eq_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν]:
    fDiv (renyiFun a) μ ν = ⊤
      ↔ ¬ Integrable (fun x ↦ renyiFun a ((∂μ/∂ν) x).toReal) ν ∨ ¬ μ ≪ ν := by
  simp [fDiv_eq_top_iff, derivAtTop_renyiFun_of_one_lt ha]

lemma fDiv_renyiFun_ne_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv (renyiFun a) μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ renyiFun a ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν := by
  simp [fDiv_ne_top_iff, derivAtTop_renyiFun_of_one_lt ha]

lemma fDiv_renyiFun_eq_top_iff_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν]:
    fDiv (renyiFun a) μ ν = ⊤ ↔ ¬ Integrable (fun x ↦ renyiFun a ((∂μ/∂ν) x).toReal) ν := by
  simp [fDiv_eq_top_iff, derivAtTop_renyiFun_of_lt_one ha_pos ha]

lemma fDiv_renyiFun_ne_top_iff_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν]:
    fDiv (renyiFun a) μ ν ≠ ⊤ ↔ Integrable (fun x ↦ renyiFun a ((∂μ/∂ν) x).toReal) ν := by
  simp [fDiv_ne_top_iff, derivAtTop_renyiFun_of_lt_one ha_pos ha]

end FDiv

open Classical in
noncomputable def renyiDiv (a : ℝ) (μ ν : Measure α) : EReal :=
  if a = 0 then - log (ν {x | 0 < (∂μ/∂ν) x}).toReal
  else if a = 1 then EReal.toReal (kl μ ν)
  else if fDiv (renyiFun a) μ ν ≠ ⊤
    then (a - 1)⁻¹ * log (1 + (a - 1) * (fDiv (renyiFun a) μ ν).toReal)
    else ⊤

lemma renyiDiv_zero (μ ν : Measure α) :
    renyiDiv 0 μ ν = - log (ν {x | 0 < (∂μ/∂ν) x}).toReal := if_pos rfl

lemma renyiDiv_one (μ ν : Measure α) : renyiDiv 1 μ ν = EReal.toReal (kl μ ν) := by
  rw [renyiDiv, if_neg (by simp), if_pos rfl]

lemma renyiDiv_eq_top_iff_fDiv_eq_top [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) :
    renyiDiv a μ ν = ⊤ ↔ fDiv (renyiFun a) μ ν = ⊤ := by
  simp only [renyiDiv, ha_pos.ne', ↓reduceIte, ha_ne_one, ne_eq, ite_not, ite_eq_left_iff]
  rw [← EReal.coe_mul]
  simp only [EReal.coe_ne_top, imp_false, not_not]

lemma renyiDiv_of_not_integrable [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_pos : 0 < a) (ha_ne_one : a ≠ 1)
    (h_int : ¬ Integrable (fun x ↦ renyiFun a ((∂μ/∂ν) x).toReal) ν) :
    renyiDiv a μ ν = ⊤ := by
  rw [renyiDiv_eq_top_iff_fDiv_eq_top ha_pos ha_ne_one]
  cases le_total 1 a with
  | inl ha =>
    rw [fDiv_renyiFun_eq_top_iff_of_one_lt (lt_of_le_of_ne ha (Ne.symm ha_ne_one))]
    exact Or.inl h_int
  | inr ha =>
    rwa [fDiv_renyiFun_eq_top_iff_of_lt_one ha_pos (lt_of_le_of_ne ha ha_ne_one)]

lemma renyiDiv_of_lt_one (μ ν : Measure α) [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_pos : 0 < a) (ha_lt_one : a < 1)
    (h_int : Integrable (fun x ↦ renyiFun a ((∂μ/∂ν) x).toReal) ν) :
    renyiDiv a μ ν
      = (a - 1)⁻¹ * log (1 + (a - 1) * (fDiv (renyiFun a) μ ν).toReal) := by
  rw [renyiDiv, if_neg ha_pos.ne', if_neg ha_lt_one.ne,
    if_pos ((fDiv_renyiFun_ne_top_iff_of_lt_one ha_pos ha_lt_one _ _).mpr h_int)]

lemma renyiDiv_of_one_lt_of_ac [IsFiniteMeasure μ] [SigmaFinite ν] (ha_one_lt : 1 < a)
    (h_int : Integrable (fun x ↦ renyiFun a ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    renyiDiv a μ ν
      = (a - 1)⁻¹ * log (1 + (a - 1) * (fDiv (renyiFun a) μ ν).toReal) := by
  rw [renyiDiv, if_neg (zero_lt_one.trans ha_one_lt).ne', if_neg ha_one_lt.ne',
    if_pos ((fDiv_renyiFun_ne_top_iff_of_one_lt ha_one_lt _ _).mpr ⟨h_int, hμν⟩)]

lemma renyiDiv_of_one_lt_of_not_ac [IsFiniteMeasure μ] [SigmaFinite ν]
    (ha_one_lt : 1 < a) (hμν : ¬ μ ≪ ν) :
    renyiDiv a μ ν = ⊤ := by
  rw [renyiDiv, if_neg (zero_lt_one.trans ha_one_lt).ne', if_neg ha_one_lt.ne',
    if_neg]
  rw [fDiv_renyiFun_ne_top_iff_of_one_lt ha_one_lt]
  push_neg
  exact fun _ ↦ hμν

end ProbabilityTheory

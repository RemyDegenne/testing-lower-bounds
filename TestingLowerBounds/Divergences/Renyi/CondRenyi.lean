/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.Hellinger.CondHellinger
import TestingLowerBounds.Divergences.Renyi.Renyi

/-!
# Conditional Rényi divergence

## Main definitions

* `condRenyiDiv a κ η μ`: the conditional Rényi divergence of order `a` between the kernels `κ`
  and `η` with respect to `μ`, defined as `renyiDiv a (μ ⊗ₘ κ) (μ ⊗ₘ η)`.

## Main statements

* `condRenyiDiv_zero`, `condRenyiDiv_one`: the special cases.
* `renyiDiv_comp_left_le`: `renyiDiv a (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condRenyiDiv a κ η μ`.

-/

open Real MeasureTheory Filter MeasurableSpace InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β} {a : ℝ}

/-- Rényi divergence between two kernels κ and η conditional to a measure μ.
It is defined as `Rₐ(κ, η | μ) := Rₐ(μ ⊗ₘ κ, μ ⊗ₘ η)`. -/
noncomputable
def condRenyiDiv (a : ℝ) (κ η : Kernel α β) (μ : Measure α) : ℝ≥0∞ :=
  renyiDiv a (μ ⊗ₘ κ) (μ ⊗ₘ η)

/-Maybe this can be stated in a nicer way, but I didn't find a way to do it. It's probably good
enough to use `condRenyiDiv_of_lt_one`.-/
lemma condRenyiDiv_zero (κ η : Kernel α β) (μ : Measure α)
    [IsFiniteKernel κ] [IsMarkovKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv 0 κ η μ
      = (- ENNReal.log ((μ ⊗ₘ η) {x | 0 < (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x} / μ .univ)).toENNReal := by
  rw [condRenyiDiv, renyiDiv_zero, Measure.compProd_apply_univ]

@[simp]
lemma condRenyiDiv_one [CountableOrCountablyGenerated α β] (κ η : Kernel α β) (μ : Measure α)
    [IsMarkovKernel κ] [IsMarkovKernel η] [IsFiniteMeasure μ] [NeZero μ] :
    condRenyiDiv 1 κ η μ = (μ .univ)⁻¹ * condKL κ η μ := by
  rw [condRenyiDiv, renyiDiv_one, Measure.compProd_apply_univ, Measure.compProd_apply_univ,
    klDiv_smul_same' (ENNReal.inv_ne_top.mpr (NeZero.ne _)), klDiv_compProd_eq_condKL]

lemma integrable_rpow_rnDeriv_compProd_right_iff [CountableOrCountablyGenerated α β]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1) (κ η : Kernel α β) (μ : Measure α)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] (h_ac : ∀ᵐ x ∂μ, κ x ≪ η x) :
    Integrable (fun x ↦ ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal ^ a) (μ ⊗ₘ η)
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
        ∧ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂(η x)) μ := by
  rw [← integrable_hellingerFun_iff_integrable_rpow ha_ne,
    integrable_f_rnDeriv_compProd_right_iff (stronglyMeasurable_hellingerFun ha_pos.le)
      (convexOn_hellingerFun ha_pos.le)]
  simp_rw [integrable_hellingerFun_iff_integrable_rpow ha_ne]
  refine and_congr_right fun h_int ↦ ?_
  have h : (fun x ↦ ∫ b, hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x)
      =ᵐ[μ] fun x ↦ (a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x
        + ((η x) .univ).toReal + (1 - a)⁻¹ * a * ((κ x) .univ).toReal := by
    filter_upwards [h_int, h_ac] with x hx_int hx_ac
    exact integral_hellingerFun_of_pos_of_ne_one_of_integrable_of_ac ha_pos ha_ne hx_int hx_ac
  rw [integrable_congr h,
    integrable_add_iff_integrable_left' ((Integrable.Kernel _ .univ).const_mul _),
    integrable_add_iff_integrable_left' (Integrable.Kernel _ .univ),
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (inv_ne_zero (sub_ne_zero.mpr ha_ne)))]

section TopAndBounds

lemma condRenyiDiv_eq_top_iff_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
    (κ η : Kernel α β) (μ : Measure α) [IsMarkovKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
    [NeZero μ] :
    condRenyiDiv a κ η μ = ⊤
      ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
        ∨ ¬ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ
        ∨ ¬ ∀ᵐ x ∂μ, κ x ≪ η x := by
  have : NeZero (μ ⊗ₘ κ) := by
    refine ⟨fun h ↦ NeZero.ne μ ?_⟩
    rw [← Measure.measure_univ_eq_zero, ← Measure.compProd_apply_univ (κ := κ), h,
      Measure.coe_zero, Pi.zero_apply]
  rw [condRenyiDiv, renyiDiv_eq_top_iff_of_one_lt ha,
    Measure.absolutelyContinuous_compProd_right_iff]
  by_cases h_ac : ∀ᵐ x ∂μ, κ x ≪ η x
  · rw [integrable_rpow_rnDeriv_compProd_right_iff (zero_lt_one.trans ha) ha.ne' κ η μ h_ac]
    tauto
  · tauto

lemma condRenyiDiv_ne_top_iff_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
    (κ η : Kernel α β) (μ : Measure α) [IsMarkovKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
    [NeZero μ] :
    condRenyiDiv a κ η μ ≠ ⊤
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
        ∧ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ
        ∧ ∀ᵐ x ∂μ, κ x ≪ η x := by
  rw [ne_eq, condRenyiDiv_eq_top_iff_of_one_lt ha]
  push Not
  rfl

lemma condRenyiDiv_eq_top_iff_of_lt_one [CountableOrCountablyGenerated α β]
    (ha_nonneg : 0 ≤ a) (ha : a < 1)
    (κ η : Kernel α β) (μ : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ = ⊤ ↔ ∀ᵐ x ∂μ, κ x ⟂ₘ η x := by
  rw [condRenyiDiv, renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_nonneg ha,
    Measure.mutuallySingular_compProd_right_iff]

lemma condRenyiDiv_of_not_ae_integrable_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
    [IsMarkovKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] [NeZero μ]
    (h_int : ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))) :
    condRenyiDiv a κ η μ = ⊤ := by
  rw [condRenyiDiv_eq_top_iff_of_one_lt ha]
  exact Or.inl h_int

lemma condRenyiDiv_of_not_integrable_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
    [IsMarkovKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] [NeZero μ]
    (h_int : ¬ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condRenyiDiv a κ η μ = ⊤ := by
  rw [condRenyiDiv_eq_top_iff_of_one_lt ha]
  exact Or.inr (Or.inl h_int)

lemma condRenyiDiv_of_not_ac_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
    [IsMarkovKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] [NeZero μ]
    (h_ac : ¬ ∀ᵐ x ∂μ, κ x ≪ η x) :
    condRenyiDiv a κ η μ = ⊤ := by
  rw [condRenyiDiv_eq_top_iff_of_one_lt ha]
  exact Or.inr (Or.inr h_ac)

lemma condRenyiDiv_of_mutuallySingular_of_lt_one [CountableOrCountablyGenerated α β]
    (ha_nonneg : 0 ≤ a) (ha : a < 1) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
    (h_ms : ∀ᵐ x ∂μ, κ x ⟂ₘ η x) :
    condRenyiDiv a κ η μ = ⊤ :=
  (condRenyiDiv_eq_top_iff_of_lt_one ha_nonneg ha κ η μ).mpr h_ms

lemma condRenyiDiv_of_ne_zero [CountableOrCountablyGenerated α β] (ha_zero : a ≠ 0)
    (ha_ne_one : a ≠ 1) (κ η : Kernel α β) (μ : Measure α) [IsFiniteKernel κ] [∀ x, NeZero (κ x)]
    [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ = ((a - 1)⁻¹ * ENNReal.log
      (((avgMass a (μ ⊗ₘ κ) (μ ⊗ₘ η) : EReal) + (a - 1) * condHellingerDiv a κ η μ).toENNReal)
      - (a - 1)⁻¹ * (a * Real.log ((μ ⊗ₘ κ) .univ).toReal
        + (1 - a) * Real.log ((μ ⊗ₘ η) .univ).toReal)).toENNReal := by
  rw [condRenyiDiv, renyiDiv_of_ne_one ha_zero ha_ne_one, hellingerDiv_compProd_left μ κ η]

end TopAndBounds

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β}

lemma renyiDiv_comp_left_le (ha_pos : 0 < a) (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    renyiDiv a (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condRenyiDiv a κ η μ :=
  le_renyiDiv_of_le_hellingerDiv ha_pos (Measure.snd_compProd μ κ ▸ Measure.snd_univ)
    (Measure.snd_compProd μ η ▸ Measure.snd_univ) (hellingerDiv_comp_le_compProd μ μ κ η)

end DataProcessingInequality

end ProbabilityTheory

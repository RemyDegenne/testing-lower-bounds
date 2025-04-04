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

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation


## Implementation details


-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β} {a : ℝ}

-- lemma integrable_rpow_rnDeriv_compProd_right_iff [CountableOrCountablyGenerated α β]
--     (ha_pos : 0 < a) (ha_one : a ≠ 1) (κ η : Kernel α β) (μ : Measure α)
--     [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
--     (h_ac : 1 ≤ a → ∀ᵐ (x : α) ∂μ, κ x ≪ η x) :
--     Integrable (fun x ↦ ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal ^ a) (μ ⊗ₘ η)
--       ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--         ∧ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂(η x)) μ := by
--   simp_rw [← integrable_hellingerFun_iff_integrable_rpow ha_one,
--     integrable_f_rnDeriv_compProd_right_iff (stronglyMeasurable_hellingerFun (by linarith))
--     (convexOn_hellingerFun (by linarith))]
--   refine and_congr_right (fun h_int ↦ ?_)
--   rw [← integrable_hellingerDiv_iff h_int h_ac]
--   refine integrable_hellingerDiv_iff' ha_pos ha_one ?_ h_ac
--   simp_rw [← integrable_hellingerFun_iff_integrable_rpow ha_one, h_int]

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
    condRenyiDiv 1 κ η μ = condKL κ η μ := by
  rw [condRenyiDiv, renyiDiv_one, kl_compProd_left]
  simp only [Measure.compProd_apply_univ, ne_eq, measure_ne_top, not_false_eq_true,
    ENNReal.toReal_toEReal_of_ne_top]
  sorry

section TopAndBounds

-- lemma condRenyiDiv_eq_top_iff_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
--     (κ η : Kernel α β) (μ : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
--     condRenyiDiv a κ η μ = ⊤
--       ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--         ∨ ¬Integrable (fun x ↦ ∫ (b : β), ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ
--         ∨ ¬ ∀ᵐ x ∂μ, κ x ≪ η x := by
--   rw [condRenyiDiv, renyiDiv_eq_top_iff_of_one_lt ha,
--     Measure.absolutelyContinuous_compProd_right_iff, ← or_assoc]
--   refine or_congr_left' fun h_ac ↦ ?_
--   rw [integrable_rpow_rnDeriv_compProd_right_iff (by linarith) ha.ne']
--   swap;· exact fun _ ↦ not_not.mp h_ac
--   tauto

-- lemma condRenyiDiv_ne_top_iff_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
--     (κ η : Kernel α β) (μ : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
--     condRenyiDiv a κ η μ ≠ ⊤
--       ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
--         ∧ Integrable (fun x ↦ ∫ (b : β), ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ
--         ∧ ∀ᵐ x ∂μ, κ x ≪ η x := by
--   rw [ne_eq, condRenyiDiv_eq_top_iff_of_one_lt ha]
--   push_neg
--   rfl

-- lemma condRenyiDiv_eq_top_iff_of_lt_one [CountableOrCountablyGenerated α β]
--     (ha_nonneg : 0 ≤ a) (ha : a < 1)
--     (κ η : Kernel α β) (μ : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
--     condRenyiDiv a κ η μ = ⊤ ↔ ∀ᵐ a ∂μ, κ a ⟂ₘ η a := by
--   rw [condRenyiDiv, renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_nonneg ha,
--     Measure.mutuallySingular_compProd_iff_of_same_left]

-- lemma condRenyiDiv_of_not_ae_integrable_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
--     [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
--     (h_int : ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))) :
--     condRenyiDiv a κ η μ = ⊤ := by
--   rw [condRenyiDiv_eq_top_iff_of_one_lt ha]
--   exact Or.inl h_int

-- lemma condRenyiDiv_of_not_integrable_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
--     [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
--     (h_int : ¬Integrable (fun x ↦ ∫ (b : β), ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
--     condRenyiDiv a κ η μ = ⊤ := by
--   rw [condRenyiDiv_eq_top_iff_of_one_lt ha]
--   exact Or.inr (Or.inl h_int)

-- lemma condRenyiDiv_of_not_ac_of_one_lt [CountableOrCountablyGenerated α β] (ha : 1 < a)
--     [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] (h_ac : ¬ ∀ᵐ x ∂μ, κ x ≪ η x) :
--     condRenyiDiv a κ η μ = ⊤ := by
--   rw [condRenyiDiv_eq_top_iff_of_one_lt ha]
--   exact Or.inr (Or.inr h_ac)

-- lemma condRenyiDiv_of_mutuallySingular_of_lt_one [CountableOrCountablyGenerated α β]
--     (ha_nonneg : 0 ≤ a) (ha : a < 1) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
--     (h_ms : ∀ᵐ x ∂μ, κ x ⟂ₘ η x) :
--     condRenyiDiv a κ η μ = ⊤ := by
--   rw [condRenyiDiv, renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_nonneg ha]
--   exact (Measure.mutuallySingular_compProd_iff_of_same_left μ κ η).mpr h_ms

-- lemma condRenyiDiv_of_ne_zero [CountableOrCountablyGenerated α β] (ha_nonneg : 0 ≤ a)
--     (ha_ne_one : a ≠ 1) (κ η : Kernel α β) (μ : Measure α) [IsFiniteKernel κ] [∀ x, NeZero (κ x)]
--     [IsFiniteKernel η] [IsFiniteMeasure μ] :
--     condRenyiDiv a κ η μ = (a - 1)⁻¹
--       * ENNReal.log (↑((μ ⊗ₘ η) .univ) + (a - 1) * (condHellingerDiv a κ η μ)).toENNReal := by
--   rw [condRenyiDiv, renyiDiv_of_ne_one ha_ne_one, hellingerDiv_compProd_left ha_nonneg _]

end TopAndBounds

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β}

lemma renyiDiv_comp_left_le [Nonempty α] [StandardBorelSpace α]
    (ha_pos : 0 < a) (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    renyiDiv a (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condRenyiDiv a κ η μ :=
  le_renyiDiv_of_le_hellingerDiv ha_pos (Measure.snd_compProd μ κ ▸ Measure.snd_univ)
    (Measure.snd_compProd μ η ▸ Measure.snd_univ) (hellingerDiv_comp_le_compProd μ μ κ η)

end DataProcessingInequality

end ProbabilityTheory

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.Unique
import TestingLowerBounds.MeasureCompProd

/-!

# Bayesian inverse (or posterior)

## Main definitions

* `bayesInv`: Bayesian inverse of a kernel

## Main statements

*

## Notation

`κ†μ` denotes the Bayesian inverse of `κ` with respect to `μ`, `bayesInv κ μ`.

## Implementation details

-/

open scoped ENNReal

open MeasureTheory

namespace ProbabilityTheory

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
    {κ : kernel α β} {μ : Measure α} [IsFiniteMeasure μ] [IsFiniteKernel κ]

variable [StandardBorelSpace α] [Nonempty α]

/-- Bayesian inverse of the kernel `κ` with respect to the measure `μ`. -/
noncomputable
def bayesInv (κ : kernel α β) (μ : Measure α) [IsFiniteMeasure μ] [IsFiniteKernel κ] : kernel β α :=
  ((μ ⊗ₘ κ).map Prod.swap).condKernel

scoped[ProbabilityTheory] notation κ "†" μ => ProbabilityTheory.bayesInv κ μ

/-- The Bayesian inverse is a Markov kernel. -/
instance : IsMarkovKernel (κ†μ) := by rw [bayesInv]; infer_instance

/-- The main property of the Bayesian inverse. -/
lemma compProd_bayesInv (κ : kernel α β) (μ : Measure α) [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    μ ∘ₘ κ ⊗ₘ (κ†μ) = (μ ⊗ₘ κ).map Prod.swap := by
  have h := Measure.compProd_fst_condKernel ((μ ⊗ₘ κ).map Prod.swap)
  rwa [Measure.fst_swap_compProd] at h

lemma compProd_bayesInv' (κ : kernel α β) (μ : Measure α) [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    μ ∘ₘ κ ∘ₘ (kernel.id ×ₖ (κ†μ)) = (μ ∘ₘ (kernel.id ×ₖ κ)).map Prod.swap := by
  simp_rw [← Measure.compProd_eq_comp]
  exact compProd_bayesInv κ μ

lemma compProd_bayesInv'' (κ : kernel α β) (μ : Measure α) [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    μ ∘ₘ κ ∘ₘ (kernel.copy β) ∘ₘ (kernel.id ∥ₖ (κ†μ))
      = μ ∘ₘ (kernel.copy α) ∘ₘ (κ ∥ₖ kernel.id) := by
  have h := compProd_bayesInv' κ μ
  rw [kernel.prod_eq_copy_comp_parallelComp, ← Measure.comp_assoc] at h
  rw [h, ← Measure.comp_deterministic_eq_map measurable_swap, kernel.prod_eq_copy_comp_parallelComp,
    ← Measure.comp_assoc, Measure.comp_assoc, ← kernel.swap, kernel.swap_parallelComp,
    ← Measure.comp_assoc]
  suffices μ ∘ₘ (kernel.copy α) ∘ₘ (kernel.swap α α) = μ ∘ₘ (kernel.copy α) by rw [this]
  rw [Measure.comp_assoc, kernel.swap_copy]

/-- The Bayesian inverse is unique up to a `μ ∘ₘ κ`-null set. -/
lemma eq_bayesInv_of_compProd_eq (η : kernel β α) [IsFiniteKernel η]
    (h : (μ ∘ₘ κ ⊗ₘ η) = (μ ⊗ₘ κ).map Prod.swap) :
    ∀ᵐ a ∂(μ ∘ₘ κ), η a = (κ†μ) a := by
  rw [← Measure.fst_swap_compProd] at h
  convert eq_condKernel_of_measure_eq_compProd η h.symm
  rw [Measure.fst_swap_compProd]

@[simp]
lemma bayesInv_comp_self [IsMarkovKernel κ] : μ ∘ₘ κ ∘ₘ (κ†μ) = μ := by
  rw [Measure.comp_eq_snd_compProd, compProd_bayesInv, Measure.snd_map_swap, Measure.fst_compProd]

/-- The Bayesian inverse is involutive (up to `μ`-a.e. equality). -/
lemma bayesInv_bayesInv [StandardBorelSpace β] [Nonempty β] [IsMarkovKernel κ] :
    ∀ᵐ a ∂μ, ((κ†μ)†(μ ∘ₘ κ)) a = κ a := by
  suffices ∀ᵐ a ∂(μ ∘ₘ κ ∘ₘ (κ†μ)), κ a = ((κ†μ)†(μ ∘ₘ κ)) a by
    rw [bayesInv_comp_self] at this
    filter_upwards [this] with a h using h.symm
  refine eq_bayesInv_of_compProd_eq κ ?_
  rw [bayesInv_comp_self, compProd_bayesInv κ μ, Measure.map_map measurable_swap measurable_swap]
  simp

/-- The Bayesian inverse of the identity kernel is the identity kernel. -/
lemma bayesInv_id : ∀ᵐ a ∂μ, (kernel.id†μ) a = kernel.id a := by
  suffices ∀ᵐ a ∂(μ ∘ₘ kernel.id), kernel.id a = ((kernel.id : kernel α α)†μ) a by
    rw [Measure.comp_id] at this
    filter_upwards [this] with a ha using ha.symm
  refine eq_bayesInv_of_compProd_eq kernel.id ?_
  rw [Measure.comp_id, Measure.compProd_id, Measure.map_map measurable_swap]
  · congr
  · exact measurable_id.prod_mk measurable_id

/-- The Bayesian inverse is contravariant. -/
lemma bayesInv_comp [StandardBorelSpace β] [Nonempty β] {η : kernel β γ} [IsFiniteKernel η] :
    ∀ᵐ c ∂(μ ∘ₘ κ ∘ₘ η), ((η ∘ₖ κ)†μ) c = ((κ†μ) ∘ₖ η†(μ ∘ₘ κ)) c := by
  suffices ∀ᵐ c ∂(μ ∘ₘ κ ∘ₘ η), ((κ†μ) ∘ₖ η†(μ ∘ₘ κ)) c = ((η ∘ₖ κ)†μ) c by
    filter_upwards [this] with _ h using h.symm
  rw [Measure.comp_assoc]
  refine eq_bayesInv_of_compProd_eq ((κ†μ) ∘ₖ η†(μ ∘ₘ κ)) ?_
  simp_rw [Measure.compProd_eq_comp, kernel.prod_eq_copy_comp_parallelComp,
    kernel.parallelComp_comp_right,
    ← Measure.comp_deterministic_eq_map measurable_swap, ← Measure.comp_assoc]
  calc μ ∘ₘ κ ∘ₘ η ∘ₘ (kernel.copy γ) ∘ₘ (kernel.id ∥ₖ η†μ ∘ₘ ⇑κ) ∘ₘ (kernel.id ∥ₖ κ†μ)
  _ = μ ∘ₘ κ ∘ₘ (kernel.copy β) ∘ₘ (η ∥ₖ kernel.id) ∘ₘ (kernel.id ∥ₖ κ†μ) := by
    rw [compProd_bayesInv'']
  _ = μ ∘ₘ κ ∘ₘ (kernel.copy β) ∘ₘ (kernel.id ∥ₖ κ†μ) ∘ₘ (η ∥ₖ kernel.id) := by
    rw [Measure.comp_assoc, kernel.parallelComp_comm, ← Measure.comp_assoc]
  _ = μ ∘ₘ (kernel.copy α) ∘ₘ (κ ∥ₖ kernel.id) ∘ₘ (η ∥ₖ kernel.id) := by
    rw [compProd_bayesInv'']
  _ = μ ∘ₘ (kernel.copy α) ∘ₘ (kernel.id ∥ₖ κ) ∘ₘ (kernel.id ∥ₖ η) ∘ₘ (kernel.swap _ _) := by
    simp_rw [Measure.comp_assoc]
    conv_rhs => rw [← kernel.comp_assoc]
    rw [kernel.swap_parallelComp, kernel.comp_assoc]
    suffices κ ∥ₖ kernel.id ∘ₖ kernel.copy α
        = (kernel.swap α β) ∘ₖ (kernel.id ∥ₖ κ ∘ₖ kernel.copy α) by
      rw [this]
    rw [← kernel.comp_assoc, kernel.swap_parallelComp, kernel.comp_assoc, kernel.swap_copy]

end ProbabilityTheory

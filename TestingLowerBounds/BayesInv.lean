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

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open scoped ENNReal

open MeasureTheory

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    [StandardBorelSpace α] [Nonempty α]
    {κ : kernel α β} {μ : Measure α} [IsFiniteMeasure μ] [IsFiniteKernel κ]

--instance {μ : Measure α} [SFinite μ] {κ : kernel α β} [IsSFiniteKernel κ] : SFinite (μ ∘ₘ κ) := by
--  rw [Measure.comp_eq_snd_compProd]
--  infer_instance

instance {μ : Measure α} [IsFiniteMeasure μ] {κ : kernel α β} [IsFiniteKernel κ] :
    IsFiniteMeasure (μ ∘ₘ κ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

@[simp]
lemma Measure.fst_map_swap {μ : Measure (α × β)} : (μ.map Prod.swap).fst = μ.snd := by
  rw [Measure.fst, Measure.map_map measurable_fst measurable_swap]
  congr

@[simp]
lemma Measure.snd_map_swap {μ : Measure (α × β)} : (μ.map Prod.swap).snd = μ.fst := by
  rw [Measure.snd, Measure.map_map measurable_snd measurable_swap]
  congr

@[simp]
lemma Measure.fst_swap_compProd : ((μ ⊗ₘ κ).map Prod.swap).fst = μ ∘ₘ κ := by
  rw [Measure.comp_eq_snd_compProd]
  simp

lemma Measure.comp_deterministic_eq_map {f : α → β} (hf : Measurable f) :
    μ ∘ₘ kernel.deterministic f hf = μ.map f := by
  ext s hs
  rw [Measure.bind_apply hs (kernel.measurable _), Measure.map_apply hf hs]
  simp only [kernel.deterministic_apply' hf _ hs]
  classical
  rw [lintegral_indicator_const_comp hf hs, one_mul]

section KernelId

/-- The identity kernel. -/
protected noncomputable
def kernel.id : kernel α α := kernel.deterministic id measurable_id

instance : IsMarkovKernel (kernel.id : kernel α α) := by rw [kernel.id]; infer_instance

lemma kernel.id_apply (a : α) : kernel.id a = Measure.dirac a := by
  rw [kernel.id, deterministic_apply, id_def]

lemma kernel.deterministic_prod_deterministic {f : α → β} {g : α → γ}
    (hf : Measurable f) (hg : Measurable g) :
    deterministic f hf ×ₖ deterministic g hg
      = deterministic (fun a ↦ (f a, g a)) (hf.prod_mk hg) := by
  ext a
  simp_rw [prod_apply, deterministic_apply]
  rw [Measure.dirac_prod_dirac]

lemma Measure.comp_id : μ ∘ₘ kernel.id = μ := by
  rw [kernel.id, Measure.comp_deterministic_eq_map, Measure.map_id]

lemma Measure.compProd_id : μ ⊗ₘ kernel.id = μ.map (fun x ↦ (x, x)) := by
  rw [Measure.compProd_eq_comp, kernel.id, kernel.deterministic_prod_deterministic,
    Measure.comp_deterministic_eq_map]
  rfl

end KernelId

/-- Bayesian inverse of the kernel `κ` with respect to the measure `μ`. -/
noncomputable
def bayesInv (κ : kernel α β) (μ : Measure α) [IsFiniteMeasure μ] [IsFiniteKernel κ] : kernel β α :=
  ((μ ⊗ₘ κ).map Prod.swap).condKernel

scoped[ProbabilityTheory] notation κ "†" μ => ProbabilityTheory.bayesInv κ μ

/-- The Bayesian inverse is a Markov kernel. -/
instance : IsMarkovKernel (κ†μ) := by rw [bayesInv]; infer_instance

/-- The main property of the Bayesian inverse. -/
lemma compProd_bayesInv (κ : kernel α β) (μ : Measure α) [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    (μ ∘ₘ κ ⊗ₘ κ†μ) = (μ ⊗ₘ κ).map Prod.swap := by
  have h := Measure.compProd_fst_condKernel ((μ ⊗ₘ κ).map Prod.swap)
  rwa [Measure.fst_swap_compProd] at h

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

lemma bayesInv_comp [StandardBorelSpace β] [Nonempty β] {η : kernel β γ} [IsFiniteKernel η] :
    ∀ᵐ c ∂(μ ∘ₘ κ ∘ₘ η), ((η ∘ₖ κ)†μ) = (κ†μ) ∘ₖ (η†(μ ∘ₘ κ)) := by
  sorry

end ProbabilityTheory

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.MeasureCompProd
import TestingLowerBounds.ForMathlib.GiryMonad
import TestingLowerBounds.Kernel.ParallelComp


/-!

# Results about the composition-product of measures

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

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : ℝ → ℝ}

/-- Composition of a measure and a kernel.

Defined using `MeasureTheory.Measure.bind` -/
scoped[ProbabilityTheory] notation3 κ " ∘ₘ " μ:100 => Measure.bind μ κ

lemma Measure.map_comp (μ : Measure α) (κ : Kernel α β) {f : β → γ} (hf : Measurable f) :
    (κ ∘ₘ μ).map f = (κ.map f) ∘ₘ μ := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.bind_apply (hf hs) κ.measurable,
    Measure.bind_apply hs (Kernel.measurable _)]
  simp_rw [Kernel.map_apply' _ hf _ hs]

lemma Measure.comp_assoc {μ : Measure α} {κ : Kernel α β} {η : Kernel β γ} :
    η ∘ₘ (κ ∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ :=
  Measure.bind_bind κ.measurable η.measurable

lemma Measure.comp_deterministic_eq_map {f : α → β} (hf : Measurable f) :
    Kernel.deterministic f hf ∘ₘ μ = μ.map f :=
  Measure.bind_dirac_eq_map μ hf

lemma Measure.comp_id : Kernel.id ∘ₘ μ = μ := by
  rw [Kernel.id, Measure.comp_deterministic_eq_map, Measure.map_id]

lemma Measure.comp_eq_snd_compProd (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ] :
    κ ∘ₘ μ = (μ ⊗ₘ κ).snd := by
  ext s hs
  rw [Measure.bind_apply hs κ.measurable, Measure.snd_apply hs, Measure.compProd_apply]
  · rfl
  · exact measurable_snd hs

lemma Measure.fst_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).fst = μ := by
  ext s
  rw [Measure.compProd, Measure.fst, ← Kernel.fst_apply, Kernel.fst_compProd, Kernel.const_apply]

lemma Measure.snd_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    (μ ⊗ₘ κ).snd = κ ∘ₘ μ := (Measure.comp_eq_snd_compProd μ κ).symm

lemma Measure.compProd_eq_comp (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    μ ⊗ₘ κ = (Kernel.id ×ₖ κ) ∘ₘ μ := by
  rw [Measure.compProd, Kernel.compProd_prodMkLeft_eq_comp]
  rfl

lemma Measure.compProd_id [SFinite μ] : μ ⊗ₘ Kernel.id = μ.map (fun x ↦ (x, x)) := by
  rw [Measure.compProd_eq_comp, Kernel.id, Kernel.deterministic_prod_deterministic,
    Measure.comp_deterministic_eq_map]
  rfl

/-- The composition product of a measure and a constant kernel is the product between the two
measures. -/
@[simp]
lemma Measure.compProd_const {ν : Measure β} [SFinite μ] [SFinite ν] :
    μ ⊗ₘ (Kernel.const α ν) = μ.prod ν := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.prod_apply hs]
  simp_rw [Kernel.const_apply]

@[simp]
lemma Measure.comp_const {ν : Measure β} : (Kernel.const α ν) ∘ₘ μ = μ .univ • ν := μ.bind_const ν

lemma Measure.compProd_apply_toReal [SFinite μ] [IsFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    ((μ ⊗ₘ κ) s).toReal = ∫ x, (κ x (Prod.mk x ⁻¹' s)).toReal ∂μ := by
  rw [Measure.compProd_apply hs, integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact ae_of_all _ (fun x ↦ by positivity)
  · exact (Kernel.measurable_kernel_prod_mk_left hs).ennreal_toReal.aestronglyMeasurable
  congr with x
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma Measure.compProd_univ_toReal [SFinite μ] [IsFiniteKernel κ] :
    ((μ ⊗ₘ κ) .univ).toReal = ∫ x, (κ x .univ).toReal ∂μ :=
  compProd_apply_toReal .univ

lemma Measure.fst_sum {ι : Type*} (μ : ι → Measure (α × β)) :
    (Measure.sum μ).fst = Measure.sum (fun n ↦ (μ n).fst) := by
  ext s hs
  rw [Measure.fst_apply hs, Measure.sum_apply, Measure.sum_apply _ hs]
  · congr with i
    rw [Measure.fst_apply hs]
  · exact measurable_fst hs

lemma Measure.snd_sum {ι : Type*} (μ : ι → Measure (α × β)) :
    (Measure.sum μ).snd = Measure.sum (fun n ↦ (μ n).snd) := by
  ext s hs
  rw [Measure.snd_apply hs, Measure.sum_apply, Measure.sum_apply _ hs]
  · congr with i
    rw [Measure.snd_apply hs]
  · exact measurable_snd hs

instance {μ : Measure (α × β)} [SFinite μ] : SFinite μ.fst :=
  ⟨fun n ↦ (sFiniteSeq μ n).fst, inferInstance, by rw [← Measure.fst_sum, sum_sFiniteSeq μ]⟩

instance {μ : Measure (α × β)} [SFinite μ] : SFinite μ.snd :=
  ⟨fun n ↦ (sFiniteSeq μ n).snd, inferInstance, by rw [← Measure.snd_sum, sum_sFiniteSeq μ]⟩

instance {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ] : SFinite (κ ∘ₘ μ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

instance {μ : Measure α} [IsFiniteMeasure μ] {κ : Kernel α β} [IsFiniteKernel κ] :
    IsFiniteMeasure (κ ∘ₘ μ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

instance {μ : Measure α} [IsProbabilityMeasure μ] {κ : Kernel α β} [IsMarkovKernel κ] :
    IsProbabilityMeasure (κ ∘ₘ μ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

lemma Measure.fst_swap_compProd [SFinite μ] [IsSFiniteKernel κ] :
    ((μ ⊗ₘ κ).map Prod.swap).fst = κ ∘ₘ μ := by
  simp [Measure.comp_eq_snd_compProd]

lemma compProd_apply_toReal [SFinite μ] [IsFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    ((μ ⊗ₘ κ) s).toReal = ∫ x, (κ x (Prod.mk x ⁻¹' s)).toReal ∂μ := by
  rw [Measure.compProd_apply hs, integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact ae_of_all _ (fun x ↦ by positivity)
  · exact (Kernel.measurable_kernel_prod_mk_left hs).ennreal_toReal.aestronglyMeasurable
  congr with x
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma compProd_univ_toReal [SFinite μ] [IsFiniteKernel κ] :
    ((μ ⊗ₘ κ) .univ).toReal = ∫ x, (κ x .univ).toReal ∂μ :=
  compProd_apply_toReal .univ

lemma Measure.compProd_apply_univ [SFinite μ] [IsMarkovKernel κ] :
    (μ ⊗ₘ κ) .univ = μ .univ := by
  rw [Measure.compProd_apply .univ]
  simp

lemma Measure.comp_apply_univ [IsMarkovKernel κ] : (κ ∘ₘ μ) .univ = μ .univ := by
  rw [Measure.bind_apply .univ κ.measurable]
  simp

lemma Measure.compProd_smul_left (a : ℝ≥0∞) [SFinite μ] [IsSFiniteKernel κ] :
    (a • μ) ⊗ₘ κ = a • (μ ⊗ₘ κ) := by
  ext s hs
  simp only [Measure.compProd_apply hs, lintegral_smul_measure, Measure.smul_apply, smul_eq_mul]

lemma Measure.comp_smul_left (a : ℝ≥0∞) : κ ∘ₘ (a • μ) = a • (κ ∘ₘ μ) := by
  ext s hs
  simp only [Measure.bind_apply hs κ.measurable, lintegral_smul_measure, Measure.smul_apply,
    smul_eq_mul]

section ParallelComp

namespace Kernel

variable {δ : Type*} {mδ : MeasurableSpace δ}

lemma _root_.MeasureTheory.Measure.prod_comp_right
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (κ : Kernel β γ) [IsSFiniteKernel κ] :
    μ.prod (κ ∘ₘ ν) = (Kernel.id ∥ₖ κ) ∘ₘ (μ.prod ν) := by
  ext s hs
  rw [Measure.prod_apply hs, Measure.bind_apply hs (Kernel.measurable _)]
  simp_rw [Measure.bind_apply (measurable_prod_mk_left hs) (Kernel.measurable _)]
  rw [MeasureTheory.lintegral_prod]
  swap; · exact (Kernel.measurable_coe _ hs).aemeasurable
  congr with a
  congr with b
  rw [parallelComp_apply, Kernel.id_apply, Measure.prod_apply hs, lintegral_dirac']
  exact measurable_measure_prod_mk_left hs

lemma _root_.MeasureTheory.Measure.prod_comp_left
    (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν]
    (κ : Kernel α γ) [IsSFiniteKernel κ] :
    (κ ∘ₘ μ).prod ν = (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) := by
  have h1 : (κ ∘ₘ μ).prod ν = (ν.prod (κ ∘ₘ μ)).map Prod.swap := by
    rw [Measure.prod_swap]
  have h2 : (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
    calc (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν)
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((ν.prod μ).map Prod.swap) := by rw [Measure.prod_swap]
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((swap _ _) ∘ₘ (ν.prod μ)) := by
      rw [swap, Measure.comp_deterministic_eq_map]
    _ = (swap _ _) ∘ₘ ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)) := by
      rw [Measure.comp_assoc, Measure.comp_assoc, swap_parallelComp]
    _ = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
      rw [swap, Measure.comp_deterministic_eq_map]
  rw [← Measure.prod_comp_right, ← h1] at h2
  exact h2.symm

lemma parallelComp_comp_right {α' : Type*} {_ : MeasurableSpace α'}
    (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α' γ) [IsSFiniteKernel η] (ξ : Kernel γ δ) [IsSFiniteKernel ξ] :
    κ ∥ₖ (ξ ∘ₖ η) = (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) := by
  ext a
  rw [parallelComp_apply, comp_apply, comp_apply, parallelComp_apply, Measure.prod_comp_right]

lemma parallelComp_comp_left {α' : Type*} {_ : MeasurableSpace α'}
    (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α' γ) [IsSFiniteKernel η] (ξ : Kernel γ δ) [IsSFiniteKernel ξ] :
    (ξ ∘ₖ η) ∥ₖ κ = (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) := by
  ext a
  rw [parallelComp_apply, comp_apply, comp_apply, parallelComp_apply, Measure.prod_comp_left]

lemma parallelComp_comm (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ κ) ∘ₖ (η ∥ₖ Kernel.id) = (η ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ κ) := by
  rw [← parallelComp_comp_right, ← parallelComp_comp_left, comp_id, comp_id]

lemma parallelComp_comp_parallelComp {α' β' γ' : Type*} {mα' : MeasurableSpace α'}
    {mβ' : MeasurableSpace β'} {mγ' : MeasurableSpace γ'}
    {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel β γ} [IsSFiniteKernel η]
    {κ' : Kernel α' β'} [IsSFiniteKernel κ'] {η' : Kernel β' γ'} [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ') := by
  rw [parallelComp_comp_right, parallelComp_comp_left, ← comp_assoc, ← parallelComp_comp_right,
    comp_id]

lemma parallelComp_comp_prod {β' γ' : Type*}
    {mβ' : MeasurableSpace β'} {mγ' : MeasurableSpace γ'}
    {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel β γ} [IsSFiniteKernel η]
    {κ' : Kernel α β'} [IsSFiniteKernel κ'] {η' : Kernel β' γ'} [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  rw [prod_eq_parallelComp_comp_copy, ← comp_assoc, parallelComp_comp_parallelComp,
    prod_eq_parallelComp_comp_copy]

lemma parallelComp_comp_id_left_right (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ η) ∘ₖ (κ ∥ₖ Kernel.id) = κ ∥ₖ η := by
  rw [← parallelComp_comp_right, comp_id]

lemma parallelComp_comp_id_right_left {κ : Kernel α β} [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η] :
    (κ ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ η) = κ ∥ₖ η := by
  rw [← parallelComp_comp_left, comp_id]

-- todo: remove?
lemma parallelComp_comp_id_left_left (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel β γ) [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ η) ∘ₖ (Kernel.id ∥ₖ κ) = (Kernel.id (mα := mδ)) ∥ₖ (η ∘ₖ κ) := by
  rw [← parallelComp_comp_right]

-- todo: remove?
lemma parallelComp_comp_id_right_right {κ : Kernel α β} [IsSFiniteKernel κ]
    (η : Kernel β γ) [IsSFiniteKernel η] :
    (η ∥ₖ Kernel.id) ∘ₖ (κ ∥ₖ Kernel.id) = (η ∘ₖ κ) ∥ₖ (Kernel.id (mα := mγ)) := by
  rw [← parallelComp_comp_left]

end Kernel

lemma Measure.parallelComp_comp_compProd [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ]
    {η : Kernel β γ} [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ η) ∘ₘ (μ ⊗ₘ κ) = μ ⊗ₘ (η ∘ₖ κ) := by
  rw [Measure.compProd_eq_comp, Measure.compProd_eq_comp, Measure.comp_assoc,
    Kernel.parallelComp_comp_prod, Kernel.id_comp]

end ParallelComp

section AbsolutelyContinuous

lemma Measure.absolutelyContinuous_comp {μ ν : Measure α} {κ η : Kernel α γ}
    [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ ν := by
  simp_rw [Measure.comp_eq_snd_compProd, Measure.snd]
  exact Measure.AbsolutelyContinuous.map (Measure.absolutelyContinuous_compProd hμν hκη)
    measurable_snd

lemma Measure.absolutelyContinuous_comp_left {μ ν : Measure α} [SFinite μ] [SFinite ν]
    (hμν : μ ≪ ν) (κ : Kernel α γ) [IsSFiniteKernel κ]  :
    κ ∘ₘ μ ≪ κ ∘ₘ ν :=
  absolutelyContinuous_comp hμν (ae_of_all μ fun _ _ a ↦ a)

lemma Measure.absolutelyContinuous_comp_right (μ : Measure α) {κ η : Kernel α γ}
    [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ μ :=
  Measure.absolutelyContinuous_comp μ.absolutelyContinuous_refl hκη

end AbsolutelyContinuous

end ProbabilityTheory

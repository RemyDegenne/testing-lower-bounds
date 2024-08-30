/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Composition
import TestingLowerBounds.Kernel.Basic

/-!

# Basic kernel definitions

Those definitions are related to the copy-delete category structure of kernels.

-/

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
  {μ : Measure α} [IsFiniteMeasure μ]
  {κ : Kernel α β}

section KernelId

/-- The identity kernel. -/
protected noncomputable
def id : Kernel α α := Kernel.deterministic id measurable_id

instance : IsMarkovKernel (Kernel.id : Kernel α α) := by rw [Kernel.id]; infer_instance

lemma id_apply (a : α) : Kernel.id a = Measure.dirac a := by
  rw [Kernel.id, deterministic_apply, id_def]

@[simp]
lemma comp_id : κ ∘ₖ Kernel.id = κ := by rw [Kernel.id, comp_deterministic_eq_comap, comap_id]

@[simp]
lemma id_comp : Kernel.id ∘ₖ κ = κ := by rw [Kernel.id, deterministic_comp_eq_map, map_id]

lemma compProd_prodMkLeft_eq_comp
    (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel β γ) [IsSFiniteKernel η] :
    κ ⊗ₖ (prodMkLeft α η) = (Kernel.id ×ₖ η) ∘ₖ κ := by
  ext a s hs
  rw [comp_eq_snd_compProd, compProd_apply _ _ _ hs, snd_apply' _ _ hs, compProd_apply]
  swap; · exact measurable_snd hs
  simp only [prodMkLeft_apply, Set.mem_setOf_eq, Set.setOf_mem_eq, prod_apply' _ _ _ hs,
    id_apply, id_eq]
  congr with b
  rw [lintegral_dirac']
  exact measurable_measure_prod_mk_left hs

end KernelId

section Copy

noncomputable
def copy (α : Type*) [MeasurableSpace α] : Kernel α (α × α) := Kernel.id ×ₖ Kernel.id

instance : IsMarkovKernel (copy α) := by rw [copy]; infer_instance

lemma copy_apply (a : α) : copy α a = Measure.dirac (a, a) := by
  rw [copy, prod_apply, id_apply, Measure.dirac_prod_dirac]

end Copy

section Discard

/-- The Markov kernel to the `Unit` type. -/
noncomputable
def discard (α : Type*) [MeasurableSpace α] : Kernel α Unit :=
  Kernel.deterministic (fun _ ↦ ()) measurable_const

instance : IsMarkovKernel (discard α) := by rw [discard]; infer_instance

@[simp]
lemma discard_apply (a : α) : discard α a = Measure.dirac () := deterministic_apply _ _

@[simp]
lemma comp_discard (κ : Kernel α β) [IsMarkovKernel κ] : discard β ∘ₖ κ = discard α := by
  ext a s hs; simp [comp_apply' _ _ _ hs]

@[simp]
lemma _root_.MeasureTheory.Measure.comp_discard (μ : Measure α) :
    μ.bind (discard α) = μ .univ • (Measure.dirac ()) := by
  ext s hs; simp [Measure.bind_apply hs (Kernel.measurable _), mul_comm]

end Discard

section Swap

noncomputable
def swap (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Kernel (α × β) (β × α) :=
  Kernel.deterministic Prod.swap measurable_swap

instance : IsMarkovKernel (swap α β) := by rw [swap]; infer_instance

lemma swap_apply (ab : α × β) : swap α β ab = Measure.dirac ab.swap := by
  rw [swap, deterministic_apply]

lemma swap_apply' (ab : α × β) {s : Set (β × α)} (hs : MeasurableSet s) :
    swap α β ab s = s.indicator 1 ab.swap := by
  rw [swap_apply, Measure.dirac_apply' _ hs]

@[simp]
lemma swap_copy : (swap α α) ∘ₖ (copy α) = copy α := by
  ext a s hs
  rw [comp_apply, copy_apply, Measure.bind_dirac (Kernel.measurable _), swap_apply' _ hs,
    Measure.dirac_apply' _ hs]
  congr

@[simp]
lemma swap_swap : (swap α β) ∘ₖ (swap β α) = Kernel.id := by
  simp_rw [swap, Kernel.deterministic_comp_deterministic, Prod.swap_swap_eq, Kernel.id]

lemma swap_comp_eq_map {κ : Kernel α (β × γ)} :
    (swap β γ) ∘ₖ κ = κ.map Prod.swap measurable_swap := by
  rw [swap, deterministic_comp_eq_map]

end Swap

section ParallelComp

noncomputable
def parallelComp (κ : Kernel α β) (η : Kernel γ δ) : Kernel (α × γ) (β × δ) :=
  (prodMkRight γ κ) ×ₖ (prodMkLeft α η)

scoped[ProbabilityTheory] infixl:100 " ∥ₖ " => ProbabilityTheory.Kernel.parallelComp

lemma parallelComp_apply (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η] (x : α × γ) :
    (κ ∥ₖ η) x = (κ x.1).prod (η x.2) := by
  rw [parallelComp, prod_apply, prodMkRight_apply, prodMkLeft_apply]

instance (κ : Kernel α β) (η : Kernel γ δ) : IsSFiniteKernel (κ ∥ₖ η) := by
  rw [parallelComp]; infer_instance

instance (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel γ δ) [IsFiniteKernel η] :
    IsFiniteKernel (κ ∥ₖ η) := by
  rw [parallelComp]; infer_instance

instance (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel γ δ) [IsMarkovKernel η] :
    IsMarkovKernel (κ ∥ₖ η) := by
  rw [parallelComp]; infer_instance

lemma prod_eq_parallelComp_comp_copy (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α γ) [IsSFiniteKernel η] :
    κ ×ₖ η = (κ ∥ₖ η) ∘ₖ (copy α) := by
  ext a s hs
  simp_rw [prod_apply, comp_apply, copy_apply, Measure.bind_apply hs (Kernel.measurable _)]
  rw [lintegral_dirac']
  swap; · exact Kernel.measurable_coe _ hs
  rw [parallelComp_apply]

lemma swap_parallelComp {κ : Kernel α β} [IsSFiniteKernel κ]
    {η : Kernel γ δ} [IsSFiniteKernel η] :
    (swap β δ) ∘ₖ (κ ∥ₖ η) = (η ∥ₖ κ) ∘ₖ (swap α γ) := by
  ext ac s hs
  rw [comp_apply, comp_apply, swap_apply, parallelComp_apply,
    Measure.bind_apply hs (Kernel.measurable _), Measure.bind_apply hs (Kernel.measurable _),
    lintegral_dirac' _ (Kernel.measurable_coe _ hs), parallelComp_apply]
  simp_rw [swap_apply' _ hs]
  change ∫⁻ (a : β × δ), s.indicator (fun _ ↦ 1) a.swap ∂(κ ac.1).prod (η ac.2) = _
  rw [lintegral_indicator_const_comp measurable_swap hs, one_mul,
    ← Measure.map_apply measurable_swap hs, Measure.prod_swap]
  rfl

--move this and PR it to mathlib, it should go right after `Kernel.measurable_Kernel_prod_mk_left'`, but in that file ∘ₖ is not defined, so maybe we should find a better place for it or modify the proof so it does not need it
lemma measurable_Kernel_prod_mk_left'' {κ : Kernel α β}
    [IsSFiniteKernel κ] {t : Set (γ × β)} (ht : MeasurableSet t) :
    Measurable (Function.uncurry fun a y ↦ (κ a) (Prod.mk y ⁻¹' t)) := by
  have h1 (p : α × γ) : (Prod.mk p.2 ⁻¹' t)
      = (Prod.mk p ⁻¹' (MeasurableEquiv.prodAssoc ⁻¹' (.univ ×ˢ t))) := by
    ext x; simp [MeasurableEquiv.prodAssoc]
  have h2 (p : α × γ) : κ p.1
      = (κ ∘ₖ (deterministic (fun (p : α × γ) ↦ p.1) measurable_fst (mα := inferInstance))) p := by
    ext s hs
    rw [comp_apply, deterministic_apply, Measure.bind_apply hs κ.measurable,
      lintegral_dirac' _ (κ.measurable_coe hs)]
  simp_rw [Function.uncurry_def, h1, h2]
  exact Kernel.measurable_kernel_prod_mk_left <| (MeasurableEquiv.measurableSet_preimage _).mpr
    (MeasurableSet.univ.prod ht)

lemma parallelComp_comp_parallelComp {α' β' γ' : Type*} {mα' : MeasurableSpace α'}
    {mβ' : MeasurableSpace β'} {mγ' : MeasurableSpace γ'}
    {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel β γ} [IsSFiniteKernel η]
    {κ' : Kernel α' β'} [IsSFiniteKernel κ'] {η' : Kernel β' γ'} [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ') := by
  ext a s hs
  simp_rw [comp_apply, parallelComp_apply]
  rw [Measure.bind_apply hs (Kernel.measurable _), Measure.prod_apply hs,
    lintegral_prod_of_measurable _ (Kernel.measurable_coe _ hs)]
  simp_rw [parallelComp_apply, comp_apply]
  have : SFinite ((κ' a.2).bind ⇑η') := by sorry --this instance is in MeasureCompProd, which imports this file, we may have to move some lemmas around or create a new file
  rw [Measure.lintegral_bind η.measurable (measurable_measure_prod_mk_left hs)]
  simp_rw [Measure.bind_apply (measurable_prod_mk_left hs) η'.measurable, Measure.prod_apply hs,
    lintegral_lintegral_swap (measurable_Kernel_prod_mk_left'' hs).aemeasurable]

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
  rw [parallelComp_comp_parallelComp, id_comp, comp_id]

lemma parallelComp_comp_id_right_left {κ : Kernel α β} [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η] :
    (κ ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ η) = κ ∥ₖ η := by
  rw [parallelComp_comp_parallelComp, id_comp, comp_id]

lemma parallelComp_comp_id_left_left (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel β γ) [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ η) ∘ₖ (Kernel.id ∥ₖ κ) = (Kernel.id (mα := mδ)) ∥ₖ (η ∘ₖ κ) := by
  rw [parallelComp_comp_parallelComp, id_comp]

lemma parallelComp_comp_id_right_right {κ : Kernel α β} [IsSFiniteKernel κ]
    (η : Kernel β γ) [IsSFiniteKernel η] :
    (η ∥ₖ Kernel.id) ∘ₖ (κ ∥ₖ Kernel.id) = (η ∘ₖ κ) ∥ₖ (Kernel.id (mα := mγ)) := by
  rw [parallelComp_comp_parallelComp, id_comp]

end ParallelComp

@[simp]
lemma swap_prod {κ : Kernel α β} [IsSFiniteKernel κ]
    {η : Kernel α γ} [IsSFiniteKernel η] :
    (swap β γ) ∘ₖ (κ ×ₖ η) = (η ×ₖ κ) := by
  simp_rw [prod_eq_parallelComp_comp_copy, ← comp_assoc, swap_parallelComp, comp_assoc, swap_copy]

end ProbabilityTheory.Kernel

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Composition

/-!

# Basic kernel definitions

Those definitions are related to the copy-delete category structure of kernels.

-/

open MeasureTheory

namespace ProbabilityTheory.kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
  {μ : Measure α} [IsFiniteMeasure μ]
  {κ : kernel α β} [IsFiniteKernel κ]

section KernelId

/-- The identity kernel. -/
protected noncomputable
def id : kernel α α := kernel.deterministic id measurable_id

instance : IsMarkovKernel (kernel.id : kernel α α) := by rw [kernel.id]; infer_instance

lemma id_apply (a : α) : kernel.id a = Measure.dirac a := by
  rw [kernel.id, deterministic_apply, id_def]

@[simp]
lemma comp_id : κ ∘ₖ kernel.id = κ := by
  ext a
  rw [comp_apply, id_apply, Measure.bind_dirac (kernel.measurable _)]

@[simp]
lemma id_comp : kernel.id ∘ₖ κ = κ := by
  ext a s hs
  simp_rw [comp_apply, Measure.bind_apply hs (kernel.measurable _), id_apply,
    Measure.dirac_apply' _ hs]
  rw [lintegral_indicator_one hs]

lemma compProd_prodMkLeft_eq_comp
    (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel β γ) [IsSFiniteKernel η] :
    κ ⊗ₖ (prodMkLeft α η) = (kernel.id ×ₖ η) ∘ₖ κ := by
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
def copy (α : Type*) [MeasurableSpace α] : kernel α (α × α) :=
  kernel.id ×ₖ kernel.id

instance : IsMarkovKernel (copy α) := by rw [copy]; infer_instance

lemma copy_apply (a : α) : copy α a = Measure.dirac (a, a) := by
  rw [copy, prod_apply, id_apply, Measure.dirac_prod_dirac]

end Copy

section Swap

noncomputable
def swap (α : Type*) [MeasurableSpace α] (β : Type*) [MeasurableSpace β] : kernel (α × β) (β × α) :=
  kernel.deterministic Prod.swap measurable_swap

instance : IsMarkovKernel (swap α β) := by rw [swap]; infer_instance

lemma swap_apply (ab : α × β) : swap α β ab = Measure.dirac ab.swap := by
  rw [swap, deterministic_apply]

lemma swap_apply' (ab : α × β) {s : Set (β × α)} (hs : MeasurableSet s) :
    swap α β ab s = s.indicator 1 ab.swap := by
  rw [swap_apply, Measure.dirac_apply' _ hs]

@[simp]
lemma swap_copy : (swap α α) ∘ₖ (copy α) = copy α := by
  ext a s hs
  rw [comp_apply, copy_apply, Measure.bind_dirac (kernel.measurable _), swap_apply' _ hs,
    Measure.dirac_apply' _ hs]
  congr

end Swap

noncomputable
def parallelComp (κ : kernel α β) (η : kernel γ δ) : kernel (α × γ) (β × δ) :=
  (prodMkRight γ κ) ×ₖ (prodMkLeft α η)

scoped[ProbabilityTheory] infixl:100 " ∥ₖ " => ProbabilityTheory.kernel.parallelComp

lemma parallelComp_apply (κ : kernel α β) [IsSFiniteKernel κ]
    (η : kernel γ δ) [IsSFiniteKernel η] (x : α × γ) :
    (κ ∥ₖ η) x = (κ x.1).prod (η x.2) := by
  rw [parallelComp, prod_apply, prodMkRight_apply, prodMkLeft_apply]

instance (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel γ δ) [IsSFiniteKernel η] :
    IsSFiniteKernel (κ ∥ₖ η) := by
  rw [parallelComp]; infer_instance

instance (κ : kernel α β) [IsFiniteKernel κ] (η : kernel γ δ) [IsFiniteKernel η] :
    IsFiniteKernel (κ ∥ₖ η) := by
  rw [parallelComp]; infer_instance

instance (κ : kernel α β) [IsMarkovKernel κ] (η : kernel γ δ) [IsMarkovKernel η] :
    IsMarkovKernel (κ ∥ₖ η) := by
  rw [parallelComp]; infer_instance

lemma prod_eq_copy_comp_parallelComp (κ : kernel α β) [IsSFiniteKernel κ]
    (η : kernel α γ) [IsSFiniteKernel η] :
    κ ×ₖ η = (κ ∥ₖ η) ∘ₖ (copy α) := by
  ext a s hs
  simp_rw [prod_apply, comp_apply, copy_apply, Measure.bind_apply hs (kernel.measurable _)]
  rw [lintegral_dirac']
  swap; · exact kernel.measurable_coe _ hs
  rw [parallelComp_apply]

lemma swap_parallelComp {κ : kernel α β} [IsSFiniteKernel κ]
    {η : kernel γ δ} [IsSFiniteKernel η] :
    (swap β δ) ∘ₖ (κ ∥ₖ η) = (η ∥ₖ κ) ∘ₖ (swap α γ) := by
  ext ac s hs
  rw [comp_apply, comp_apply, swap_apply, parallelComp_apply,
    Measure.bind_apply hs (kernel.measurable _),
    Measure.bind_apply hs (kernel.measurable _), lintegral_dirac', parallelComp_apply]
  · simp_rw [swap_apply' _ hs]
    change ∫⁻ (a : β × δ), s.indicator (fun _ ↦ 1) a.swap ∂(κ ac.1).prod (η ac.2) = _
    rw [lintegral_indicator_const_comp measurable_swap hs, one_mul,
      ← Measure.map_apply measurable_swap hs, Measure.prod_swap]
    rfl
  · exact kernel.measurable_coe _ hs

end ProbabilityTheory.kernel

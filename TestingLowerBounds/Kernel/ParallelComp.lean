/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Kernel.DeterministicComp

/-!

# Parallel composition of kernels

-/

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

section ParallelComp

-- todo: give direct definition, and use this to build compProd?
/-- Parallel product of two kernels. -/
noncomputable
def parallelComp (κ : Kernel α β) (η : Kernel γ δ) : Kernel (α × γ) (β × δ) :=
  (prodMkRight γ κ) ×ₖ (prodMkLeft α η)

@[inherit_doc]
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

end ParallelComp

--todo: move.
@[simp]
lemma swap_prod {κ : Kernel α β} [IsSFiniteKernel κ]
    {η : Kernel α γ} [IsSFiniteKernel η] :
    (swap β γ) ∘ₖ (κ ×ₖ η) = (η ×ₖ κ) := by
  simp_rw [prod_eq_parallelComp_comp_copy, ← comp_assoc, swap_parallelComp, comp_assoc, swap_copy]

end ProbabilityTheory.Kernel

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!

# Parallel composition of kernels

-/

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

section ParallelComp

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
    rw [comp_apply, deterministic_apply, Measure.bind_apply hs (aemeasurable _),
      lintegral_dirac' _ (κ.measurable_coe hs)]
  simp_rw [Function.uncurry_def, h1, h2]
  refine measurable_kernel_prodMk_left ?_
  refine (MeasurableEquiv.measurableSet_preimage _).mpr ?_
  exact MeasurableSet.univ.prod ht

end ParallelComp

end ProbabilityTheory.Kernel

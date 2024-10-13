/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Composition
import TestingLowerBounds.Kernel.Deterministic

/-!

# Composition-related properties of basic deterministic kernels

-/

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {κ : Kernel α β}

section KernelId

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

section Discard

@[simp]
lemma comp_discard (κ : Kernel α β) [IsMarkovKernel κ] : discard β ∘ₖ κ = discard α := by
  ext a s hs; simp [comp_apply' _ _ _ hs]

end Discard

section Swap

@[simp]
lemma swap_copy : (swap α α) ∘ₖ (copy α) = copy α := by
  ext a s hs
  rw [comp_apply, copy_apply, Measure.dirac_bind (Kernel.measurable _), swap_apply' _ hs,
    Measure.dirac_apply' _ hs]
  congr

@[simp]
lemma swap_swap : (swap α β) ∘ₖ (swap β α) = Kernel.id := by
  simp_rw [swap, Kernel.deterministic_comp_deterministic, Prod.swap_swap_eq, Kernel.id]

lemma swap_comp_eq_map {κ : Kernel α (β × γ)} : (swap β γ) ∘ₖ κ = κ.map Prod.swap := by
  rw [swap, deterministic_comp_eq_map]

end Swap

end ProbabilityTheory.Kernel

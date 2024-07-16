/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Composition

/-!

# Basic kernel definitions

-/

open MeasureTheory

namespace ProbabilityTheory.kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

lemma snd_compProd_prodMkLeft
    (κ : kernel α β) (η : kernel β γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    snd (κ ⊗ₖ prodMkLeft α η) = η ∘ₖ κ := by
  ext a s hs
  rw [snd_apply' _ _ hs, compProd_apply, comp_apply' _ _ _ hs]
  · rfl
  · exact measurable_snd hs

lemma map_comp (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel β γ) [IsSFiniteKernel η]
    {f : γ → δ} (hf : Measurable f) :
    kernel.map (η ∘ₖ κ) f hf = (kernel.map η f hf) ∘ₖ κ := by
  ext a s hs
  rw [map_apply' _ hf _ hs, comp_apply', comp_apply' _ _ _ hs]
  · simp_rw [map_apply' _ hf _ hs]
  · exact hf hs

lemma fst_comp (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel β (γ × δ)) [IsSFiniteKernel η] :
    fst (η ∘ₖ κ) = fst η ∘ₖ κ :=
  kernel.map_comp κ η measurable_fst

lemma snd_comp (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel β (γ × δ)) [IsSFiniteKernel η] :
    snd (η ∘ₖ κ) = snd η ∘ₖ κ :=
  kernel.map_comp κ η measurable_snd

lemma deterministic_prod_deterministic {f : α → β} {g : α → γ}
    (hf : Measurable f) (hg : Measurable g) :
    deterministic f hf ×ₖ deterministic g hg
      = deterministic (fun a ↦ (f a, g a)) (hf.prod_mk hg) := by
  ext a
  simp_rw [prod_apply, deterministic_apply]
  rw [Measure.dirac_prod_dirac]

lemma deterministic_comp_deterministic {f : α → β} {g : β → γ}
    (hf : Measurable f) (hg : Measurable g) :
    (kernel.deterministic g hg) ∘ₖ (kernel.deterministic f hf) = kernel.deterministic (g ∘ f) (hg.comp hf) := by
  ext a
  simp_rw [kernel.comp_deterministic_eq_comap, comap_apply, deterministic_apply]
  rfl

end ProbabilityTheory.kernel

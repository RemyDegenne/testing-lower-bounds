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

namespace ProbabilityTheory.Kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

lemma snd_compProd_prodMkLeft
    (κ : Kernel α β) (η : Kernel β γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    snd (κ ⊗ₖ prodMkLeft α η) = η ∘ₖ κ := by
  ext a s hs
  rw [snd_apply' _ _ hs, compProd_apply, comp_apply' _ _ _ hs]
  · rfl
  · exact measurable_snd hs

lemma map_comp (κ : Kernel α β) (η : Kernel β γ) {f : γ → δ} (hf : Measurable f) :
    Kernel.map (η ∘ₖ κ) f hf = (Kernel.map η f hf) ∘ₖ κ := by
  ext a s hs
  rw [map_apply' _ hf _ hs, comp_apply', comp_apply' _ _ _ hs]
  · simp_rw [map_apply' _ hf _ hs]
  · exact hf hs

lemma fst_comp (κ : Kernel α β) (η : Kernel β (γ × δ)) :
    fst (η ∘ₖ κ) = fst η ∘ₖ κ :=
  Kernel.map_comp κ η measurable_fst

lemma snd_comp (κ : Kernel α β) (η : Kernel β (γ × δ)) :
    snd (η ∘ₖ κ) = snd η ∘ₖ κ :=
  Kernel.map_comp κ η measurable_snd

lemma deterministic_prod_deterministic {f : α → β} {g : α → γ}
    (hf : Measurable f) (hg : Measurable g) :
    deterministic f hf ×ₖ deterministic g hg
      = deterministic (fun a ↦ (f a, g a)) (hf.prod_mk hg) := by
  ext a
  simp_rw [prod_apply, deterministic_apply]
  rw [Measure.dirac_prod_dirac]

lemma deterministic_comp_deterministic {f : α → β} {g : β → γ}
    (hf : Measurable f) (hg : Measurable g) :
    (Kernel.deterministic g hg) ∘ₖ (Kernel.deterministic f hf) = Kernel.deterministic (g ∘ f) (hg.comp hf) := by
  ext a
  simp_rw [Kernel.comp_deterministic_eq_comap, comap_apply, deterministic_apply]
  rfl

end ProbabilityTheory.Kernel

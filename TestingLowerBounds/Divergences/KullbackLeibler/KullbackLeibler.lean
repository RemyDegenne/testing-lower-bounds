/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import TestingLowerBounds.Divergences.KullbackLeibler.KLDivFun
import TestingLowerBounds.FDiv.Basic

/-!
# Kullback-Leibler divergence

The Kullback-Leibler divergence `klDiv` is defined in Mathlib (`InformationTheory.klDiv`).
This file relates it to the f-divergence for the divergence function `klDivFun`.

## Main statements

* `klDiv_eq_fDiv`: `klDiv μ ν = fDiv klDivFun μ ν`

-/

open Real MeasureTheory Filter MeasurableSpace Set InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

lemma fDiv_klDivFun_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv klDivFun μ ν = ∞ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ := by
  rw [fDiv_eq_top_iff]
  simp only [derivAtTop_klDivFun, true_and]
  by_cases hμν : μ ≪ ν
  · rw [lintegral_klDivFun_eq_top_iff hμν]
    tauto
  · simp [hμν]

lemma klDiv_eq_fDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = fDiv klDivFun μ ν := by
  classical
  by_cases hμν : μ ≪ ν
  swap; · rw [fDiv_of_not_ac derivAtTop_klDivFun hμν, klDiv_of_not_ac hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [fDiv_of_derivAtTop_eq_top derivAtTop_klDivFun, klDiv_of_ac_of_integrable hμν h_int,
      ite_eq_left hμν]
    exact (lintegral_klDivFun_eq_integral hμν h_int).symm
  · rw [klDiv_of_not_integrable h_int, fDiv_of_lintegral_eq_top]
    exact lintegral_klDivFun_of_not_integrable hμν h_int

lemma measurable_klDiv {β : Type*} [MeasurableSpace β] [CountableOrCountablyGenerated α β]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦ klDiv (κ a) (η a)) := by
  simp_rw [klDiv_eq_fDiv]
  exact measurable_fDiv _ _

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β}

lemma klDiv_comp_le_compProd [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (κ ∘ₘ μ) (η ∘ₘ ν) ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simp_rw [klDiv_eq_fDiv]
  exact fDiv_comp_le_compProd μ ν κ η

end DataProcessingInequality

end ProbabilityTheory

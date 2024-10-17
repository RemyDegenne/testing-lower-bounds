/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.FDiv.CompProd.CompProd
import TestingLowerBounds.FDiv.Trim
import TestingLowerBounds.ForMathlib.RNDerivEqCondexp
import TestingLowerBounds.Sorry.Jensen

/-!

# Data processing inequality for f-divergences

-/

open MeasureTheory Set

open scoped ENNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ : Kernel α β} {f : ℝ → ℝ}

lemma fDiv_comp_le_compProd_right (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsFiniteKernel κ]
    (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) := by
  simp_rw [Measure.comp_eq_snd_compProd]
  exact fDiv_map_le measurable_snd hf hf_cvx hf_cont

/--The **Data Processing Inequality** for the f-divergence. -/
theorem fDiv_comp_right_le'' (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν :=
  (fDiv_comp_le_compProd_right μ ν κ hf hf_cvx hf_cont).trans_eq
    (fDiv_compProd_right μ ν κ hf hf_cvx)

-- todo: unused.
/-- To prove the DPI for an f-divergence, it suffices to prove it under an absolute continuity
hypothesis. -/
lemma fDiv_comp_le_of_comp_le_of_ac [IsFiniteMeasure ν]
    (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Ici 0) f) (κ : Kernel α β) [IsMarkovKernel κ]
    (h : ∀ μ : Measure α, IsFiniteMeasure μ → μ ≪ ν → fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν)
    (μ : Measure α) [IsFiniteMeasure μ] :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν := by
  conv_lhs => rw [← Measure.rnDeriv_add_singularPart μ ν, Measure.comp_add_right]
  refine (fDiv_add_measure_le _ _ _ hf h_cvx).trans ?_
  rw [fDiv_eq_add_withDensity_derivAtTop μ ν h_cvx, Measure.comp_apply_univ]
  exact add_le_add (h _ inferInstance (withDensity_absolutelyContinuous _ _)) le_rfl


end ProbabilityTheory

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import TestingLowerBounds.FDiv.CompProd
public import TestingLowerBounds.FDiv.Trim

/-!

# Data processing inequality for f-divergences, through Jensen's inequality

The lemmas `fDiv_fst_le''`, `fDiv_snd_le''`, `le_fDiv_compProd''`, `fDiv_comp_le_compProd''` and
`fDiv_comp_right_le''` are the data processing inequalities of `TestingLowerBounds.FDiv.CompProd`
(`fDiv_fst_le`, `fDiv_snd_le`, `le_fDiv_compProd`, `fDiv_comp_le_compProd`, `fDiv_comp_right_le`),
proved through the data processing inequality for measurable maps `fDiv_map_le`, which rests on
Jensen's inequality for the conditional Lebesgue expectation. The proofs in
`TestingLowerBounds.FDiv.CompProd` go through the disintegration of the composition-product and
need assumptions on the measurable spaces (`StandardBorelSpace`, `CountableOrCountablyGenerated`);
the versions here hold without any such assumption.

-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ : Kernel α β} {f : DivFunction}

lemma fDiv_fst_le'' (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ.fst ν.fst ≤ fDiv f μ ν :=
  fDiv_map_le measurable_fst

lemma fDiv_snd_le'' (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ.snd ν.snd ≤ fDiv f μ ν :=
  fDiv_map_le measurable_snd

/-- Composing with Markov kernels can only increase an f-divergence, even with different kernels
on the two sides. -/
lemma le_fDiv_compProd'' (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    fDiv f μ ν ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  have h := fDiv_fst_le'' (f := f) (μ ⊗ₘ κ) (ν ⊗ₘ η)
  rwa [Measure.fst_compProd, Measure.fst_compProd] at h

lemma fDiv_comp_le_compProd'' (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simp_rw [← Measure.snd_compProd]
  exact fDiv_snd_le'' _ _

/-- The **Data Processing Inequality** for the f-divergence, proved through Jensen's inequality
for conditional expectations. Compare with `fDiv_comp_right_le`, which is proved through the
disintegration of the composition-product and needs `StandardBorelSpace α`. -/
theorem fDiv_comp_right_le'' (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν :=
  (fDiv_comp_le_compProd'' μ ν κ κ).trans_eq (fDiv_compProd_left μ ν κ)

end ProbabilityTheory

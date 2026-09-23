/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

/-!
# Absolute continuity of the composition-product of kernels, pointwise

-/

@[expose] public section

open MeasureTheory MeasurableSpace ProbabilityTheory

open scoped ENNReal

lemma ProbabilityTheory.Kernel.absolutelyContinuous_compProd_iff
    {α β γ : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β} {_ : MeasurableSpace γ}
    [CountableOrCountablyGenerated β γ] {κ₁ η₁ : Kernel α β}
    {κ₂ η₂ : Kernel (α × β) γ} [IsSFiniteKernel κ₁] [IsSFiniteKernel η₁] [IsFiniteKernel κ₂]
    [IsFiniteKernel η₂] (a : α) [∀ b, NeZero (κ₂ (a, b))] :
    (κ₁ ⊗ₖ κ₂) a ≪ (η₁ ⊗ₖ η₂) a ↔ κ₁ a ≪ η₁ a ∧ ∀ᵐ b ∂κ₁ a, κ₂ (a, b) ≪ η₂ (a, b) := by
  simp_rw [Kernel.compProd_apply_eq_compProd_sectR]
  exact Measure.absolutelyContinuous_compProd_iff'

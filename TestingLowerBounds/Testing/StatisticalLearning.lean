/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Kernel.BayesInv

/-!

# Statistical learning and decision theory basics

`Θ` is the type of parameters
`𝒳` is the type of observed data

On those two types, we are given one of three (related) things:
* a joint measure `ν : Measure (Θ × 𝒳)`
* `π : Measure Θ` and `P : Kernel Θ 𝒳`
* `μ : Measure 𝒳` and `Q : Kernel 𝒳 Θ`

In parametric statistics, `Θ` is the parameter space and `P` is the known law of the data given
the parameter. The goal might be to estimate the parameter (`𝒵 = Θ`).

An estimator is a kernel `κ : Kernel 𝒳 𝒵` from the data `𝒳` to the type of predictions `𝒵`.
The estimator is evaluated based on a risk function `ℓ : Kernel (Θ × 𝒵) ℝ≥0∞`. This is usually
a deterministic kernel (a plain measurable function).

In statistical learning theory `𝒳 = 𝒳' × 𝒴`, `𝒵` is a subset of `𝒳 → 𝒴` (or of `Kernel 𝒳 𝒴`)...
and it does not work :(
There is:
* an unknown `Measure : 𝒳' × 𝒴`, which disintegrates into `Measure 𝒳'` and `Kernel 𝒳' 𝒴`
* an estimator, `Kernel (𝒳' × 𝒴)^n ℋ` where `ℋ` is a subset of `𝒳 → 𝒴`
* a loss, `ℓ : ℋ × (Kernel 𝒳' 𝒴) → ℝ≥0∞`

-/

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {Θ 𝒳 𝒴 𝒵 : Type*} {mΘ : MeasurableSpace Θ}
  {m𝒳 : MeasurableSpace 𝒳} {m𝒴 : MeasurableSpace 𝒴} {m𝒵 : MeasurableSpace 𝒵}
  {π : Measure Θ} {μ : Measure 𝒳} {ν : Measure (Θ × 𝒳)}
  {P : Kernel Θ 𝒳} {Q : Kernel 𝒳 Θ}
  {κ : Kernel 𝒳 𝒵} {ℓ : Kernel (Θ × 𝒵) ℝ≥0∞}

noncomputable
def paramRiskKernel (ℓ : Kernel (Θ × 𝒵) ℝ≥0∞) (P : Kernel Θ 𝒳) (κ : Kernel 𝒳 𝒵) :
    Kernel Θ ℝ≥0∞ :=
  ℓ ∘ₖ (Kernel.id ×ₖ (κ ∘ₖ P))

noncomputable
def dataRiskKernel (ℓ : Kernel (Θ × 𝒵) ℝ≥0∞) (Q : Kernel 𝒳 Θ) (κ : Kernel 𝒳 𝒵) :
    Kernel 𝒳 ℝ≥0∞ :=
  ℓ ∘ₖ (Q ×ₖ κ)

noncomputable
def bayesianParamRisk (ℓ : Kernel (Θ × 𝒵) ℝ≥0∞) (P : Kernel Θ 𝒳) (κ : Kernel 𝒳 𝒵)
    (π : Measure Θ) :
    Measure ℝ≥0∞ :=
  paramRiskKernel ℓ P κ ∘ₘ π

noncomputable
def bayesianDataRisk (ℓ : Kernel (Θ × 𝒵) ℝ≥0∞) (Q : Kernel 𝒳 Θ) (κ : Kernel 𝒳 𝒵)
    (μ : Measure 𝒳) :
    Measure ℝ≥0∞ :=
  dataRiskKernel ℓ Q κ ∘ₘ μ

noncomputable
def jointRiskMeasure (ℓ : Kernel (Θ × 𝒵) ℝ≥0∞) (κ : Kernel 𝒳 𝒵) (ν : Measure (Θ × 𝒳)) :
    Measure ℝ≥0∞ :=
  (ℓ ∘ₖ (Kernel.id ∥ₖ κ)) ∘ₘ ν

noncomputable
def paramRisk (ℓ : Kernel (Θ × 𝒵) ℝ≥0∞) (P : Kernel Θ 𝒳) (κ : Kernel 𝒳 𝒵) (π : Measure Θ) :
    ℝ≥0∞ :=
  ∫⁻ x, x ∂ bayesianParamRisk ℓ P κ π

noncomputable
def dataRisk (ℓ : Kernel (Θ × 𝒵) ℝ≥0∞) (Q : Kernel 𝒳 Θ) (κ : Kernel 𝒳 𝒵) (μ : Measure 𝒳) :
    ℝ≥0∞ :=
  ∫⁻ x, x ∂ bayesianDataRisk ℓ Q κ μ

noncomputable
def jointRisk (ℓ : Kernel (Θ × 𝒵) ℝ≥0∞) (κ : Kernel 𝒳 𝒵) (ν : Measure (Θ × 𝒳)) : ℝ≥0∞ :=
  ∫⁻ x, x ∂ jointRiskMeasure ℓ κ ν

noncomputable
def minParamRisk (ℓ : Kernel (Θ × 𝒵) ℝ≥0∞) (P : Kernel Θ 𝒳) (π : Measure Θ) : ℝ≥0∞ :=
  ⨅ (κ : Kernel 𝒳 𝒵) (_ : IsMarkovKernel κ), paramRisk ℓ P κ π

noncomputable
def minDataRisk (ℓ : Kernel (Θ × 𝒵) ℝ≥0∞) (Q : Kernel 𝒳 Θ) (μ : Measure 𝒳) : ℝ≥0∞ :=
  ⨅ (κ : Kernel 𝒳 𝒵) (_ : IsMarkovKernel κ), dataRisk ℓ Q κ μ

noncomputable
def minJointRisk (ℓ : Kernel (Θ × 𝒵) ℝ≥0∞) (ν : Measure (Θ × 𝒳)) : ℝ≥0∞ :=
  ⨅ (κ : Kernel 𝒳 𝒵) (_ : IsMarkovKernel κ), jointRisk ℓ κ ν

lemma bayesianParamRisk_eq_jointRiskMeasure [IsSFiniteKernel ℓ] [IsSFiniteKernel P]
    [IsSFiniteKernel κ] [SFinite π] :
    bayesianParamRisk ℓ P κ π = jointRiskMeasure ℓ κ (π ⊗ₘ P) := by
  rw [bayesianParamRisk, paramRiskKernel, jointRiskMeasure, Measure.compProd_eq_comp,
    Measure.comp_assoc, Kernel.comp_assoc, Kernel.parallelComp_comp_prod]
  simp

lemma bayesianDataRisk_eq_jointRiskMeasure [IsSFiniteKernel ℓ] [IsSFiniteKernel Q]
    [IsSFiniteKernel κ] [SFinite μ] :
    bayesianDataRisk ℓ Q κ μ = jointRiskMeasure ℓ κ ((μ ⊗ₘ Q).map Prod.swap) := by
  rw [bayesianDataRisk, dataRiskKernel, jointRiskMeasure, ← Measure.comp_deterministic_eq_map,
    ← Kernel.swap, Measure.compProd_eq_comp, Measure.comp_assoc, Measure.comp_assoc]
  simp [Kernel.comp_assoc, Kernel.swap_prod, Kernel.parallelComp_comp_prod]

lemma bayesianDataRisk_bayesInv [StandardBorelSpace Θ] [Nonempty Θ]
    [IsSFiniteKernel ℓ] [IsFiniteKernel P] [IsSFiniteKernel κ] [IsFiniteMeasure π] :
    bayesianDataRisk ℓ (P†π) κ (P ∘ₘ π) = bayesianParamRisk ℓ P κ π := by
  rw [bayesianParamRisk_eq_jointRiskMeasure, bayesianDataRisk_eq_jointRiskMeasure,
    compProd_bayesInv''', ← Measure.comp_deterministic_eq_map, ← Kernel.swap, Measure.comp_assoc,
    Kernel.swap_swap, Measure.comp_id]

lemma bayesianParamRisk_bayesInv [StandardBorelSpace 𝒳] [Nonempty 𝒳]
    [IsSFiniteKernel ℓ] [IsFiniteKernel Q] [IsSFiniteKernel κ] [IsFiniteMeasure μ] :
    bayesianParamRisk ℓ (Q†μ) κ (Q ∘ₘ μ) = bayesianDataRisk ℓ Q κ μ := by
  rw [bayesianParamRisk_eq_jointRiskMeasure, bayesianDataRisk_eq_jointRiskMeasure,
    compProd_bayesInv''', ← Measure.comp_deterministic_eq_map, ← Kernel.swap]

-- def empiricalRisk

end ProbabilityTheory

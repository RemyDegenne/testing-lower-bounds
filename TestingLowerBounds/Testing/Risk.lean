/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.ForMathlib.RadonNikodym

/-!
# Estimation and risk

## Main definitions

* `estimationProblem`
* ...

## Main statements

* `bayesRiskPrior_le_bayesRiskPrior_comp`

## Notation

## Implementation details

-/

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝒳 𝒳' 𝒴 𝒵 : Type*} {mΘ : MeasurableSpace Θ} {m𝒳 : MeasurableSpace 𝒳}
  {_ : MeasurableSpace 𝒳'} {m𝒴 : MeasurableSpace 𝒴} {m𝒵 : MeasurableSpace 𝒵}
  {μ ν : Measure 𝒳}

/-- An estimation problem: a kernel `P` from a parameter space `Θ` to a sample space `𝒳`,
an objective function `y` on the parameter space and a cost function `ℓ`. -/
@[ext]
structure estimationProblem (Θ 𝒳 𝒴 𝒵 : Type*) [mΘ : MeasurableSpace Θ]
    [m𝒳 : MeasurableSpace 𝒳] [m𝒴 : MeasurableSpace 𝒴] [m𝒵 : MeasurableSpace 𝒵] :=
  P : kernel Θ 𝒳
  y : Θ → 𝒴
  y_meas : Measurable y
  ℓ : 𝒴 × 𝒵 → ℝ≥0∞
  ℓ_meas : Measurable ℓ

@[simps]
noncomputable
def estimationProblem.comp (E : estimationProblem Θ 𝒳 𝒴 𝒵) (η : kernel 𝒳 𝒳') :
    estimationProblem Θ 𝒳' 𝒴 𝒵 where
  P := η ∘ₖ E.P
  y := E.y
  y_meas := E.y_meas
  ℓ := E.ℓ
  ℓ_meas := E.ℓ_meas

noncomputable
def risk (E : estimationProblem Θ 𝒳 𝒴 𝒵) (κ : kernel 𝒳 𝒵) (θ : Θ) : ℝ≥0∞ :=
  ∫⁻ z, E.ℓ (E.y θ, z) ∂((κ ∘ₖ E.P) θ)

noncomputable
def bayesianRisk (E : estimationProblem Θ 𝒳 𝒴 𝒵) (κ : kernel 𝒳 𝒵) (π : Measure Θ) : ℝ≥0∞ :=
  ∫⁻ θ, risk E κ θ ∂π

lemma bayesianRisk_le_iSup_risk (E : estimationProblem Θ 𝒳 𝒴 𝒵) (κ : kernel 𝒳 𝒵)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesianRisk E κ π ≤ ⨆ θ, risk E κ θ := by
  rw [bayesianRisk]
  calc ∫⁻ θ, risk E κ θ ∂π
  _ ≤ ∫⁻ _, (⨆ θ', risk E κ θ') ∂π := lintegral_mono (fun θ ↦ le_iSup _ _)
  _ = ⨆ θ, risk E κ θ := by simp

noncomputable
def bayesRiskPrior (E : estimationProblem Θ 𝒳 𝒴 𝒵) (π : Measure Θ) : ℝ≥0∞ :=
  ⨅ (κ : kernel 𝒳 𝒵) (_ : IsMarkovKernel κ), bayesianRisk E κ π

/-- **Data processing inequality** for the Bayes risk with respect to a prior. -/
lemma bayesRiskPrior_le_bayesRiskPrior_comp (E : estimationProblem Θ 𝒳 𝒴 𝒵) (π : Measure Θ)
    (η : kernel 𝒳 𝒳') [IsMarkovKernel η] :
    bayesRiskPrior E π ≤ bayesRiskPrior (E.comp η) π := by
  simp only [bayesRiskPrior, bayesianRisk, risk, estimationProblem.comp_P, estimationProblem.comp_y,
    estimationProblem.comp_ℓ]
  simp only [le_iInf_iff]
  intro κ hκ
  rw [← kernel.comp_assoc κ η]
  exact iInf_le_of_le (κ ∘ₖ η) (iInf_le_of_le inferInstance le_rfl)

def IsBayesEstimator (E : estimationProblem Θ 𝒳 𝒴 𝒵) (κ : kernel 𝒳 𝒵) (π : Measure Θ) : Prop :=
  bayesianRisk E κ π = bayesRiskPrior E π

noncomputable
def bayesRisk (E : estimationProblem Θ 𝒳 𝒴 𝒵) : ℝ≥0∞ :=
  ⨆ (π : Measure Θ) (_ : IsProbabilityMeasure π), bayesRiskPrior E π

noncomputable
def minimaxRisk (E : estimationProblem Θ 𝒳 𝒴 𝒵) : ℝ≥0∞ :=
  ⨅ (κ : kernel 𝒳 𝒵) (_ : IsMarkovKernel κ), ⨆ θ, risk E κ θ

lemma bayesRiskPrior_le_minimaxRisk (E : estimationProblem Θ 𝒳 𝒴 𝒵)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesRiskPrior E π ≤ minimaxRisk E :=
  iInf_mono (fun _ ↦ iInf_mono fun _ ↦ bayesianRisk_le_iSup_risk _ _ _)

lemma bayesRisk_le_minimaxRisk (E : estimationProblem Θ 𝒳 𝒴 𝒵) :
    bayesRisk E ≤ minimaxRisk E := by
  simp only [bayesRisk, iSup_le_iff]
  exact fun _ _ ↦ bayesRiskPrior_le_minimaxRisk _ _

end ProbabilityTheory

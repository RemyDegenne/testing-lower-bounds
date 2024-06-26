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

variable {Θ Θ' 𝒳 𝒳' 𝒳'' 𝒴 𝒵 : Type*} {mΘ : MeasurableSpace Θ} {mΘ' : MeasurableSpace Θ'}
  {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'} {m𝒳'' : MeasurableSpace 𝒳''}
  {m𝒴 : MeasurableSpace 𝒴} {m𝒵 : MeasurableSpace 𝒵}
  {μ ν : Measure 𝒳}

section EstimationProblem

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

@[simps]
noncomputable
def estimationProblem.comap (E : estimationProblem Θ 𝒳 𝒴 𝒵) (f : Θ' → Θ) (hf : Measurable f) :
    estimationProblem Θ' 𝒳 𝒴 𝒵 where
  P := kernel.comap E.P f hf
  y := E.y ∘ f
  y_meas := E.y_meas.comp hf
  ℓ := E.ℓ
  ℓ_meas := E.ℓ_meas

@[simp]
lemma estimationProblem.comp_comp (E : estimationProblem Θ 𝒳 𝒴 𝒵) (κ : kernel 𝒳 𝒳')
    (η : kernel 𝒳' 𝒳'') [IsSFiniteKernel η] :
    (E.comp κ).comp η = E.comp (η ∘ₖ κ) := by
  ext <;> simp [kernel.comp_assoc]

end EstimationProblem

/-- The risk of an estimator `κ` on an estimation problem `E` at the parameter `θ`. -/
noncomputable
def risk (E : estimationProblem Θ 𝒳 𝒴 𝒵) (κ : kernel 𝒳 𝒵) (θ : Θ) : ℝ≥0∞ :=
  ∫⁻ z, E.ℓ (E.y θ, z) ∂((κ ∘ₖ E.P) θ)

/-- The bayesian risk of an estimator `κ` on an estimation problem `E` with respect to
a prior `π`. -/
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

lemma bayesianRisk_comap_measurableEquiv (E : estimationProblem Θ 𝒳 𝒴 𝒵) [IsSFiniteKernel E.P]
    (κ : kernel 𝒳 𝒵) [IsSFiniteKernel κ] (π : Measure Θ) (e : Θ ≃ᵐ Θ') :
    bayesianRisk (E.comap e.symm e.symm.measurable) κ (π.map e) = bayesianRisk E κ π := by
  simp only [bayesianRisk, risk, estimationProblem.comap_P, estimationProblem.comap_y,
    Function.comp_apply, estimationProblem.comap_ℓ]
  rw [lintegral_map _ e.measurable]
  · congr with θ
    congr -- todo: `congr with z hz` gives a warning. bug.
    ext z hz
    · rw [kernel.comp_apply' _ _ _ hz, kernel.comp_apply' _ _ _ hz, kernel.comap_apply]
      simp
    · simp
  · refine Measurable.lintegral_kernel_prod_right ?_
    refine E.ℓ_meas.comp ?_
    exact (E.y_meas.comp (e.symm.measurable.comp measurable_fst)).prod_mk measurable_snd

/-- The Bayes risk of an estimation problem `E` with respect to a prior `π`, defined as the infimum
of the Bayesian risks of all estimators. -/
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

/-- An estimator is a Bayes estimator for a prior `π` if it attains the Bayes risk for `π`. -/
def IsBayesEstimator (E : estimationProblem Θ 𝒳 𝒴 𝒵) (κ : kernel 𝒳 𝒵) (π : Measure Θ) : Prop :=
  bayesianRisk E κ π = bayesRiskPrior E π

/-- The Bayes risk of an estimation problem `E`, defined as the supremum over priors of the Bayes
risk of `E` with respect to the prior. -/
noncomputable
def bayesRisk (E : estimationProblem Θ 𝒳 𝒴 𝒵) : ℝ≥0∞ :=
  ⨆ (π : Measure Θ) (_ : IsProbabilityMeasure π), bayesRiskPrior E π

/-- The Bayes risk of an estimation problem `E`, defined as the infimum over estimators of the
maximal risk of the estimator. -/
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

/-! ### Bayes risk increase -/

noncomputable
def bayesRiskIncrease (E : estimationProblem Θ 𝒳 𝒴 𝒵) (π : Measure Θ) (η : kernel 𝒳 𝒳') : ℝ≥0∞ :=
  bayesRiskPrior (E.comp η) π - bayesRiskPrior E π

lemma bayesRiskIncrease_comp (E : estimationProblem Θ 𝒳 𝒴 𝒵) (π : Measure Θ) (κ : kernel 𝒳 𝒳')
    [IsMarkovKernel κ] (η : kernel 𝒳' 𝒳'') [IsMarkovKernel η] :
    bayesRiskIncrease E π (η ∘ₖ κ) = bayesRiskIncrease E π κ + bayesRiskIncrease (E.comp κ) π η := by
  simp only [bayesRiskIncrease, ← estimationProblem.comp_comp]
  rw [add_comm, tsub_add_tsub_cancel]
  · exact bayesRiskPrior_le_bayesRiskPrior_comp _ _ _
  · exact bayesRiskPrior_le_bayesRiskPrior_comp _ _ _

lemma le_bayesRiskIncrease_comp (E : estimationProblem Θ 𝒳 𝒴 𝒵) (π : Measure Θ) (κ : kernel 𝒳 𝒳')
    [IsMarkovKernel κ] (η : kernel 𝒳' 𝒳'') [IsMarkovKernel η] :
    bayesRiskIncrease (E.comp κ) π η ≤ bayesRiskIncrease E π (η ∘ₖ κ) := by
  simp [bayesRiskIncrease_comp]

end ProbabilityTheory

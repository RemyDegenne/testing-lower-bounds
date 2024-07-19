/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Kernel.BayesInv
import TestingLowerBounds.ForMathlib.KernelConstComp

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

@[simps]
noncomputable
def estimationProblem.compProd (E : estimationProblem Θ 𝒳 𝒴 𝒵) (κ : kernel (Θ × 𝒳) 𝒳') :
    estimationProblem Θ (𝒳 × 𝒳') 𝒴 𝒵 where
  P := E.P ⊗ₖ κ
  y := E.y
  y_meas := E.y_meas
  ℓ := E.ℓ
  ℓ_meas := E.ℓ_meas

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

/-! ### Properties of the Bayes risk of a prior -/

lemma bayesRiskPrior_compProd_le_bayesRiskPrior (E : estimationProblem Θ 𝒳 𝒴 𝒵)
    [IsSFiniteKernel E.P] (π : Measure Θ)
    (κ : kernel (Θ × 𝒳) 𝒳') [IsMarkovKernel κ] :
    bayesRiskPrior (E.compProd κ) π ≤ bayesRiskPrior E π := by
  have : E = (E.compProd κ).comp (kernel.deterministic (fun (x, _) ↦ x) (by fun_prop)) := by
    ext
    · rw [estimationProblem.comp, estimationProblem.compProd, kernel.comp_apply,
        Measure.comp_deterministic_eq_map, ← kernel.fst_apply, kernel.fst_compProd]
    rfl; rfl
  nth_rw 2 [this]
  exact bayesRiskPrior_le_bayesRiskPrior_comp _ _ _

-- Do we also need a version without the `IsMarkovKernel` assumption? it would be of the form:
-- `bayesRiskPrior E π ≤ ⨅ z : 𝒵, ∫⁻ θ, E.ℓ (E.y θ, z) * (E.P θ) Set.univ ∂π`
lemma bayesRiskPrior_le_inf (E : estimationProblem Θ 𝒳 𝒴 𝒵) (π : Measure Θ) [IsMarkovKernel E.P] :
    bayesRiskPrior E π ≤ ⨅ z : 𝒵, ∫⁻ θ, E.ℓ (E.y θ, z) ∂π := by
  simp_rw [le_iInf_iff, bayesRiskPrior]
  refine fun z ↦ iInf_le_of_le (kernel.const _ (Measure.dirac z)) ?_
  convert iInf_le _ ?_ using 1
  · simp_rw [bayesianRisk, risk, kernel.const_comp', kernel.const_apply]
    congr with θ
    rw [lintegral_dirac']
    have := E.ℓ_meas
    fun_prop [E.ℓ_meas]
  · exact kernel.isMarkovKernel_const

/-- The Bayesian risk of an estimator `κ` with respect to a prior `π` can be expressed as an integral in the following way: `R_π(κ) = ((P†π × κ) ∘ P ∘ π)[(θ, z) ↦ ℓ(y(θ), z)]`. -/
lemma bayesianRisk_eq_lintegral_bayesInv_prod [StandardBorelSpace Θ] [Nonempty Θ]
    (E : estimationProblem Θ 𝒳 𝒴 𝒵) [IsMarkovKernel E.P] (κ : kernel 𝒳 𝒵)
    (π : Measure Θ) [IsFiniteMeasure π] [IsSFiniteKernel κ] :
    bayesianRisk E κ π = ∫⁻ (θz : Θ × 𝒵), E.ℓ (E.y θz.1, θz.2) ∂(π ∘ₘ E.P ∘ₘ ((E.P†π) ×ₖ κ)) := by
  have := E.ℓ_meas
  have := E.y_meas
  simp only [bayesianRisk, risk]
  rw [← MeasureTheory.Measure.lintegral_compProd (f := fun θz ↦ E.ℓ (E.y θz.1, θz.2)) (by fun_prop),
    ← kernel.swap_prod, kernel.prod_eq_copy_comp_parallelComp, Measure.compProd_eq_comp,
    kernel.prod_eq_copy_comp_parallelComp]
  nth_rw 2 [← kernel.parallelComp_comp_id_right_left]
  simp_rw [← Measure.comp_assoc, compProd_bayesInv'', Measure.comp_assoc, ← kernel.comp_assoc,
  kernel.swap_parallelComp, kernel.comp_assoc (_ ∥ₖ κ), kernel.swap_parallelComp, kernel.comp_assoc,
  kernel.swap_copy, ← kernel.comp_assoc, kernel.parallelComp_comp_id_left_left]

lemma bayesianRisk_ge_lintegral_iInf_bayesInv [StandardBorelSpace Θ] [Nonempty Θ]
    (E : estimationProblem Θ 𝒳 𝒴 𝒵) [IsMarkovKernel E.P] (κ : kernel 𝒳 𝒵)
    (π : Measure Θ) [IsFiniteMeasure π] [IsMarkovKernel κ] :
    bayesianRisk E κ π ≥ ∫⁻ x, ⨅ z : 𝒵, ∫⁻ θ, E.ℓ (E.y θ, z) ∂((E.P†π) x) ∂(π ∘ₘ E.P) := by
  have := E.ℓ_meas
  have := E.y_meas
  rw [bayesianRisk_eq_lintegral_bayesInv_prod,
    Measure.lintegral_bind (kernel.measurable ((E.P†π) ×ₖ κ)) (by fun_prop)]
  gcongr with x
  rw [kernel.prod_apply, lintegral_prod_symm' _ (by fun_prop)]
  calc
    _ ≥ ∫⁻ _, ⨅ z, ∫⁻ (θ : Θ), E.ℓ (E.y θ, z) ∂(E.P†π) x ∂κ x :=
      lintegral_mono fun z ↦ iInf_le' _ z
    _ = ⨅ z, ∫⁻ (θ : Θ), E.ℓ (E.y θ, z) ∂(E.P†π) x := by
      rw [lintegral_const, measure_univ, mul_one]

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

/-- **Data processing inequality** for the Bayes risk increase. -/
lemma bayesRiskIncrease_discard_comp_le_bayesRiskIncrease (E : estimationProblem Θ 𝒳 𝒴 𝒵)
    (π : Measure Θ) (κ : kernel 𝒳 𝒳') [IsMarkovKernel κ] :
    bayesRiskIncrease (E.comp κ) π (kernel.discard 𝒳')
      ≤ bayesRiskIncrease E π (kernel.discard 𝒳) := by
  convert le_bayesRiskIncrease_comp E π κ (kernel.discard 𝒳')
  simp

end ProbabilityTheory

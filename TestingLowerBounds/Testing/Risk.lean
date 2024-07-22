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
  {μ ν : Measure 𝒳} {P : kernel Θ 𝒳} {κ : kernel 𝒳 𝒵} {π : Measure Θ}

section EstimationProblem

/-- An estimation problem: a kernel `P` from a parameter space `Θ` to a sample space `𝒳`,
an objective function `y` on the parameter space and a cost function `ℓ`.
We don't put the data generating kernel into this structure, since we will often perform operations
on it and we don't want to duplicate all kernel operations on `estimationProblem`. -/
@[ext]
structure estimationProblem (Θ 𝒴 𝒵 : Type*) [mΘ : MeasurableSpace Θ]
    [m𝒴 : MeasurableSpace 𝒴] [m𝒵 : MeasurableSpace 𝒵] :=
  /-- The objective function. -/
  y : Θ → 𝒴
  y_meas : Measurable y
  /-- The cost (or loss) function. -/
  ℓ : 𝒴 × 𝒵 → ℝ≥0∞
  ℓ_meas : Measurable ℓ

/-- Given an estimation problem `E` and a measurable function `f : Θ' → Θ`, we can consider a new
estimation problem where the kernel is given by the pullback of `E.P` through `f`. -/
@[simps]
noncomputable
def estimationProblem.comap (E : estimationProblem Θ 𝒴 𝒵) (f : Θ' → Θ) (hf : Measurable f) :
    estimationProblem Θ' 𝒴 𝒵 where
  y := E.y ∘ f
  y_meas := E.y_meas.comp hf
  ℓ := E.ℓ
  ℓ_meas := E.ℓ_meas

end EstimationProblem

variable {E : estimationProblem Θ 𝒴 𝒵}

/-- The risk of an estimator `κ` on an estimation problem `E` with data generating kernel `P`
at the parameter `θ`. -/
noncomputable
def risk (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳) (κ : kernel 𝒳 𝒵) (θ : Θ) : ℝ≥0∞ :=
  ∫⁻ z, E.ℓ (E.y θ, z) ∂((κ ∘ₖ P) θ)

/-- The bayesian risk of an estimator `κ` on an estimation problem `E` with data generating
kernel `P` with respect to a prior `π`. -/
noncomputable
def bayesianRisk (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳)
    (κ : kernel 𝒳 𝒵) (π : Measure Θ) : ℝ≥0∞ :=
  ∫⁻ θ, risk E P κ θ ∂π

@[simp]
lemma bayesianRisk_of_isEmpty [IsEmpty Θ] : bayesianRisk E P κ π = 0 := by simp [bayesianRisk]

lemma bayesianRisk_le_iSup_risk (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳) (κ : kernel 𝒳 𝒵)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesianRisk E P κ π ≤ ⨆ θ, risk E P κ θ := by
  rw [bayesianRisk]
  calc ∫⁻ θ, risk E P κ θ ∂π
  _ ≤ ∫⁻ _, (⨆ θ', risk E P κ θ') ∂π := lintegral_mono (fun θ ↦ le_iSup _ _)
  _ = ⨆ θ, risk E P κ θ := by simp

lemma bayesianRisk_comap_measurableEquiv (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳)
    [IsSFiniteKernel P]
    (κ : kernel 𝒳 𝒵) [IsSFiniteKernel κ] (π : Measure Θ) (e : Θ ≃ᵐ Θ') :
    bayesianRisk (E.comap e.symm e.symm.measurable) (kernel.comap P e.symm e.symm.measurable)
      κ (π.map e) = bayesianRisk E P κ π := by
  simp only [bayesianRisk, risk, estimationProblem.comap_y, Function.comp_apply,
    estimationProblem.comap_ℓ]
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
def bayesRiskPrior (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳) (π : Measure Θ) : ℝ≥0∞ :=
  ⨅ (κ : kernel 𝒳 𝒵) (_ : IsMarkovKernel κ), bayesianRisk E P κ π

/-- **Data processing inequality** for the Bayes risk with respect to a prior. -/
lemma bayesRiskPrior_le_bayesRiskPrior_comp (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳)
    (π : Measure Θ) (η : kernel 𝒳 𝒳') [IsMarkovKernel η] :
    bayesRiskPrior E P π ≤ bayesRiskPrior E (η ∘ₖ P) π := by
  simp only [bayesRiskPrior, bayesianRisk, risk, le_iInf_iff]
  intro κ hκ
  rw [← kernel.comp_assoc κ η]
  exact iInf_le_of_le (κ ∘ₖ η) (iInf_le_of_le inferInstance le_rfl)

/-- An estimator is a Bayes estimator for a prior `π` if it attains the Bayes risk for `π`. -/
def IsBayesEstimator (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳)
    (κ : kernel 𝒳 𝒵) (π : Measure Θ) : Prop :=
  bayesianRisk E P κ π = bayesRiskPrior E P π

/-- The Bayes risk of an estimation problem `E`, defined as the supremum over priors of the Bayes
risk of `E` with respect to the prior. -/
noncomputable
def bayesRisk (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳) : ℝ≥0∞ :=
  ⨆ (π : Measure Θ) (_ : IsProbabilityMeasure π), bayesRiskPrior E P π

/-- The Bayes risk of an estimation problem `E`, defined as the infimum over estimators of the
maximal risk of the estimator. -/
noncomputable
def minimaxRisk (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳) : ℝ≥0∞ :=
  ⨅ (κ : kernel 𝒳 𝒵) (_ : IsMarkovKernel κ), ⨆ θ, risk E P κ θ

lemma bayesRiskPrior_le_minimaxRisk (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesRiskPrior E P π ≤ minimaxRisk E P :=
  iInf_mono (fun _ ↦ iInf_mono fun _ ↦ bayesianRisk_le_iSup_risk _ _ _ _)

lemma bayesRisk_le_minimaxRisk (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳) :
    bayesRisk E P ≤ minimaxRisk E P := by
  simp only [bayesRisk, iSup_le_iff]
  exact fun _ _ ↦ bayesRiskPrior_le_minimaxRisk _ _ _

/-! ### Properties of the Bayes risk of a prior -/

lemma bayesRiskPrior_compProd_le_bayesRiskPrior (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳)
    [IsSFiniteKernel P] (π : Measure Θ) (κ : kernel (Θ × 𝒳) 𝒳') [IsMarkovKernel κ] :
    bayesRiskPrior E (P ⊗ₖ κ) π ≤ bayesRiskPrior E P π := by
  have : P = (kernel.deterministic Prod.fst (by fun_prop)) ∘ₖ (P ⊗ₖ κ) := by
    rw [kernel.deterministic_comp_eq_map, ← kernel.fst, kernel.fst_compProd]
  nth_rw 2 [this]
  exact bayesRiskPrior_le_bayesRiskPrior_comp _ _ _ _

-- Do we also need a version without the `IsMarkovKernel` assumption? it would be of the form:
-- `bayesRiskPrior E π ≤ ⨅ z : 𝒵, ∫⁻ θ, E.ℓ (E.y θ, z) * (E.P θ) Set.univ ∂π`
lemma bayesRiskPrior_le_inf (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳)
    (π : Measure Θ) [IsMarkovKernel P] :
    bayesRiskPrior E P π ≤ ⨅ z : 𝒵, ∫⁻ θ, E.ℓ (E.y θ, z) ∂π := by
  simp_rw [le_iInf_iff, bayesRiskPrior]
  refine fun z ↦ iInf_le_of_le (kernel.const _ (Measure.dirac z)) ?_
  convert iInf_le _ ?_ using 1
  · simp_rw [bayesianRisk, risk, kernel.const_comp', kernel.const_apply]
    congr with θ
    rw [lintegral_dirac']
    have := E.ℓ_meas
    fun_prop [E.ℓ_meas]
  · exact kernel.isMarkovKernel_const

/-- The Bayesian risk of an estimator `κ` with respect to a prior `π` can be expressed as
an integral in the following way: `R_π(κ) = ((P†π × κ) ∘ P ∘ π)[(θ, z) ↦ ℓ(y(θ), z)]`. -/
lemma bayesianRisk_eq_lintegral_bayesInv_prod [StandardBorelSpace Θ] [Nonempty Θ]
    (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳) [IsFiniteKernel P] (κ : kernel 𝒳 𝒵)
    (π : Measure Θ) [IsFiniteMeasure π] [IsSFiniteKernel κ] :
    bayesianRisk E P κ π = ∫⁻ (θz : Θ × 𝒵), E.ℓ (E.y θz.1, θz.2) ∂(π ∘ₘ P ∘ₘ ((P†π) ×ₖ κ)) := by
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

lemma bayesianRisk_eq_integral_integral_integral [StandardBorelSpace Θ] [Nonempty Θ]
    (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳) [IsFiniteKernel P] (κ : kernel 𝒳 𝒵)
    (π : Measure Θ) [IsFiniteMeasure π] [IsSFiniteKernel κ] :
    bayesianRisk E P κ π = ∫⁻ x, ∫⁻ z, ∫⁻ θ, E.ℓ (E.y θ, z) ∂(P†π) x ∂κ x ∂π ∘ₘ P := by
  have := E.ℓ_meas
  have := E.y_meas
  rw [bayesianRisk_eq_lintegral_bayesInv_prod,
    Measure.lintegral_bind (kernel.measurable ((P†π) ×ₖ κ)) (by fun_prop)]
  congr with x
  rw [kernel.prod_apply, lintegral_prod_symm' _ (by fun_prop)]

lemma bayesianRisk_ge_lintegral_iInf_bayesInv [StandardBorelSpace Θ] [Nonempty Θ]
    (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳) [IsFiniteKernel P] (κ : kernel 𝒳 𝒵)
    (π : Measure Θ) [IsFiniteMeasure π] [IsMarkovKernel κ] :
    bayesianRisk E P κ π ≥ ∫⁻ x, ⨅ z : 𝒵, ∫⁻ θ, E.ℓ (E.y θ, z) ∂((P†π) x) ∂(π ∘ₘ P) := by
  rw [bayesianRisk_eq_integral_integral_integral]
  gcongr with x
  calc
    _ ≥ ∫⁻ _, ⨅ z, ∫⁻ (θ : Θ), E.ℓ (E.y θ, z) ∂(P†π) x ∂κ x :=
      lintegral_mono fun z ↦ iInf_le' _ z
    _ = ⨅ z, ∫⁻ (θ : Θ), E.ℓ (E.y θ, z) ∂(P†π) x := by
      rw [lintegral_const, measure_univ, mul_one]

/-! ### Generalized Bayes estimator -/

/-- We say that a measurable function `f : 𝒳 → 𝒵` is a Generalized Bayes estimator for the
estimation problem `E` with respect to the prior `π` if for `(π ∘ₘ P)`-almost every `x` it is of
the form `x ↦ argmin_z P†π(x)[θ ↦ ℓ(y(θ), z)]`.-/
structure IsGenBayesEstimator [StandardBorelSpace Θ] [Nonempty Θ]
    (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳) [IsFiniteKernel P] (f : 𝒳 → 𝒵)
    (π : Measure Θ) [IsFiniteMeasure π] : Prop where
  measurable : Measurable f
  property : ∀ᵐ x ∂π ∘ₘ P, ∫⁻ θ, E.ℓ (E.y θ, f x) ∂(P†π) x
    = ⨅ z, ∫⁻ θ, E.ℓ (E.y θ, z) ∂(P†π) x

/-- Given a Generalized Bayes estimator `f`, we can define a deterministic kernel. -/
noncomputable
abbrev IsGenBayesEstimator.kernel [StandardBorelSpace Θ] [Nonempty Θ]
    {E : estimationProblem Θ 𝒴 𝒵} {P : kernel Θ 𝒳} [IsFiniteKernel P]
    {π : Measure Θ} [IsFiniteMeasure π]
    {f : 𝒳 → 𝒵} (h : IsGenBayesEstimator E P f π) : kernel 𝒳 𝒵 :=
  kernel.deterministic f h.measurable

lemma bayesianRisk_of_isGenBayesEstimator [StandardBorelSpace Θ] [Nonempty Θ]
    {E : estimationProblem Θ 𝒴 𝒵} {P : kernel Θ 𝒳} [IsFiniteKernel P]
    {π : Measure Θ} [IsFiniteMeasure π]
    {f : 𝒳 → 𝒵} (hf : IsGenBayesEstimator E P f π) :
    bayesianRisk E P hf.kernel π
      = ∫⁻ x, ⨅ z, ∫⁻ θ, E.ℓ (E.y θ, z) ∂(P†π) x ∂π ∘ₘ P := by
  have := E.ℓ_meas
  have := E.y_meas
  rw [bayesianRisk_eq_integral_integral_integral]
  refine lintegral_congr_ae ?_
  filter_upwards [hf.property] with x hx
  rwa [kernel.deterministic_apply,
    lintegral_dirac' _ (Measurable.lintegral_prod_left (by fun_prop))]

lemma isBayesEstimator_of_isGenBayesEstimator [StandardBorelSpace Θ] [Nonempty Θ]
    {E : estimationProblem Θ 𝒴 𝒵} {P : kernel Θ 𝒳} [IsFiniteKernel P]
    {π : Measure Θ} [IsFiniteMeasure π]
    {f : 𝒳 → 𝒵} (hf : IsGenBayesEstimator E P f π) :
    IsBayesEstimator E P hf.kernel π := by
  simp_rw [IsBayesEstimator, bayesRiskPrior]
  apply le_antisymm
  · rw [bayesianRisk_of_isGenBayesEstimator hf]
    simp_all [bayesianRisk_ge_lintegral_iInf_bayesInv]
  · refine iInf_le_of_le hf.kernel ?_
    exact iInf_le _ (kernel.isMarkovKernel_deterministic hf.measurable)

/-- The estimation problem `E` admits a Generalized Bayes estimator with respect to
the prior `π`. -/
class HasGenBayesEstimator [StandardBorelSpace Θ] [Nonempty Θ] (E : estimationProblem Θ 𝒴 𝒵)
    (P : kernel Θ 𝒳) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] where
  /-- The Generalized Bayes estimator. -/
  estimator : 𝒳 → 𝒵
  property : IsGenBayesEstimator E P estimator π

lemma bayesRiskPrior_eq_of_hasGenBayesEstimator [StandardBorelSpace Θ] [Nonempty Θ]
    (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳) [IsFiniteKernel P]
    (π : Measure Θ) [IsFiniteMeasure π]
    [h : HasGenBayesEstimator E P π] :
    bayesRiskPrior E P π = ∫⁻ x, ⨅ z, ∫⁻ θ, E.ℓ (E.y θ, z) ∂((P†π) x) ∂(π ∘ₘ P) := by
  rw [← isBayesEstimator_of_isGenBayesEstimator h.property, bayesianRisk_of_isGenBayesEstimator]

/-! ### Bayes risk increase -/

/-- The Bayes risk increase of an estimation problem `E` with respect to a prior `π` and a kernel
`η` gives us how much the composition with `η` increases the risk of `E` with respect to `π`. -/
noncomputable
def bayesRiskIncrease (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳) (π : Measure Θ)
    (η : kernel 𝒳 𝒳') : ℝ≥0∞ :=
  bayesRiskPrior E (η ∘ₖ P) π - bayesRiskPrior E P π

lemma bayesRiskIncrease_comp (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳)
    (π : Measure Θ) (κ : kernel 𝒳 𝒳') [IsMarkovKernel κ] (η : kernel 𝒳' 𝒳'') [IsMarkovKernel η] :
    bayesRiskIncrease E P π (η ∘ₖ κ)
      = bayesRiskIncrease E P π κ + bayesRiskIncrease E (κ ∘ₖ P) π η := by
  simp only [bayesRiskIncrease]
  rw [add_comm, tsub_add_tsub_cancel, kernel.comp_assoc]
  · exact bayesRiskPrior_le_bayesRiskPrior_comp _ _ _ _
  · exact bayesRiskPrior_le_bayesRiskPrior_comp _ _ _ _

lemma le_bayesRiskIncrease_comp (E : estimationProblem Θ 𝒴 𝒵) (P : kernel Θ 𝒳)
    (π : Measure Θ) (κ : kernel 𝒳 𝒳') [IsMarkovKernel κ] (η : kernel 𝒳' 𝒳'') [IsMarkovKernel η] :
    bayesRiskIncrease E (κ ∘ₖ P) π η ≤ bayesRiskIncrease E P π (η ∘ₖ κ) := by
  simp [bayesRiskIncrease_comp]

/-- **Data processing inequality** for the Bayes risk increase. -/
lemma bayesRiskIncrease_discard_comp_le_bayesRiskIncrease (E : estimationProblem Θ 𝒴 𝒵)
    (P : kernel Θ 𝒳) (π : Measure Θ) (κ : kernel 𝒳 𝒳') [IsMarkovKernel κ] :
    bayesRiskIncrease E (κ ∘ₖ P) π (kernel.discard 𝒳')
      ≤ bayesRiskIncrease E P π (kernel.discard 𝒳) := by
  convert le_bayesRiskIncrease_comp E P π κ (kernel.discard 𝒳')
  simp

end ProbabilityTheory

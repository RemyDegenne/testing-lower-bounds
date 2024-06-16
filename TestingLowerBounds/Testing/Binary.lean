/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Testing.Risk
import TestingLowerBounds.MeasureCompProd
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Simple Bayesian binary hypothesis testing

## Main definitions

* `simpleBinaryHypTest`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝒳 𝒳' 𝒴 𝒵 : Type*} {mΘ : MeasurableSpace Θ} {m𝒳 : MeasurableSpace 𝒳}
  {m𝒳' : MeasurableSpace 𝒳'} {m𝒴 : MeasurableSpace 𝒴} {m𝒵 : MeasurableSpace 𝒵}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞}

/-- The kernel that sends `false` to `μ` and `true` to `ν`. -/
def twoHypKernel (μ ν : Measure 𝒳) : kernel Bool 𝒳 where
  val := fun b ↦ bif b then ν else μ
  property := measurable_discrete _

@[simp] lemma twoHypKernel_true : twoHypKernel μ ν true = ν := rfl

@[simp] lemma twoHypKernel_false : twoHypKernel μ ν false = μ := rfl

@[simp] lemma twoHypKernel_apply (b : Bool) : twoHypKernel μ ν b = bif b then ν else μ := rfl

@[simp]
lemma comp_twoHypKernel (κ : kernel 𝒳 𝒴) :
    κ ∘ₖ (twoHypKernel μ ν) = twoHypKernel (μ ∘ₘ κ) (ν ∘ₘ κ) := by
  ext b : 1
  rw [kernel.comp_apply]
  cases b with
  | false => simp
  | true => simp

@[simps]
noncomputable
def simpleBinaryHypTest (μ ν : Measure 𝒳) : estimationProblem Bool 𝒳 Bool Bool where
  P := twoHypKernel μ ν
  y := id
  y_meas := measurable_id
  ℓ := fun (y, z) ↦ if y = z then 0 else 1
  ℓ_meas := measurable_discrete _

@[simp]
lemma simpleBinaryHypTest_comp (μ ν : Measure 𝒳) (η : kernel 𝒳 𝒳') :
    (simpleBinaryHypTest μ ν).comp η = simpleBinaryHypTest (μ ∘ₘ η) (ν ∘ₘ η) := by
  ext <;> simp

@[simp]
lemma risk_simpleBinaryHypTest_true (μ ν : Measure 𝒳) (κ : kernel 𝒳 Bool) :
    risk (simpleBinaryHypTest μ ν) κ true = (ν ∘ₘ κ) {false} := by
  simp only [risk, simpleBinaryHypTest, comp_twoHypKernel, twoHypKernel_apply, cond_true, id_eq,
    Bool.true_eq, MeasurableSpace.measurableSet_top]
  calc ∫⁻ z, if z = true then 0 else 1 ∂(ν ∘ₘ κ)
  _ = ∫⁻ z, Set.indicator {false} (fun _ ↦ 1) z ∂(ν ∘ₘ κ) := by
    congr with z
    rw [Set.indicator_apply]
    classical
    simp only [Set.mem_singleton_iff]
    split_ifs with h1 h2 h2
    · exact absurd (h2.symm.trans h1) Bool.false_ne_true
    · rfl
    · rfl
    · simp at h1 h2
      exact absurd (h1.symm.trans h2) Bool.false_ne_true
  _ = (ν ∘ₘ ⇑κ) {false} := lintegral_indicator_one (measurableSet_singleton _)

@[simp]
lemma risk_simpleBinaryHypTest_false (μ ν : Measure 𝒳) (κ : kernel 𝒳 Bool) :
    risk (simpleBinaryHypTest μ ν) κ false = (μ ∘ₘ κ) {true} := by
  simp only [risk, simpleBinaryHypTest, comp_twoHypKernel, twoHypKernel_apply, cond_false, id_eq,
    Bool.false_eq, MeasurableSpace.measurableSet_top]
  calc ∫⁻ z, if z = false then 0 else 1 ∂(μ ∘ₘ κ)
  _ = ∫⁻ z, Set.indicator {true} (fun _ ↦ 1) z ∂(μ ∘ₘ κ) := by
    congr with z
    rw [Set.indicator_apply]
    classical
    simp only [Set.mem_singleton_iff]
    split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) Bool.false_ne_true
    · rfl
    · rfl
    · simp at h1 h2
      exact absurd (h2.symm.trans h1) Bool.false_ne_true
  _ = (μ ∘ₘ ⇑κ) {true} := lintegral_indicator_one (measurableSet_singleton _)

-- TODO: in the definition below, remove the `p ≤ 1` hypothesis?

/-- The Bayes risk of simple binary hypothesis testing with respect to a Bernoulli prior. -/
noncomputable
def bayesBinaryRisk (μ ν : Measure 𝒳) (p : ℝ≥0∞) (hp : p ≤ 1) : ℝ≥0∞ :=
  bayesRiskPrior (simpleBinaryHypTest μ ν) (PMF.bernoulli p hp).toMeasure

lemma bayesBinaryRisk_eq (μ ν : Measure 𝒳) (hp : p ≤ 1) :
    bayesBinaryRisk μ ν p hp
      = ⨅ (κ : kernel 𝒳 Bool) (_ : IsMarkovKernel κ),
        p * (ν ∘ₘ κ) {false} + (1 - p) * (μ ∘ₘ κ) {true} := by
  rw [bayesBinaryRisk, bayesRiskPrior]
  congr with κ
  congr with _
  rw [bayesianRisk, lintegral_fintype, mul_comm p, mul_comm (1 - p)]
  simp

/-- **Data processing inequality** for the Bayes binary risk. -/
lemma bayesBinaryRisk_le_bayesBinaryRisk_comp (μ ν : Measure 𝒳) (hp : p ≤ 1)
    (η : kernel 𝒳 𝒳') [IsMarkovKernel η] :
    bayesBinaryRisk μ ν p hp ≤ bayesBinaryRisk (μ ∘ₘ η) (ν ∘ₘ η) p hp :=
  (bayesRiskPrior_le_bayesRiskPrior_comp _ _ η).trans_eq (by simp [bayesBinaryRisk])

lemma bayesBinaryRisk_self (μ : Measure 𝒳) (hp : p ≤ 1) :
    bayesBinaryRisk μ μ p hp = min p (1 - p) := by
  rw [bayesBinaryRisk_eq]
  sorry

lemma bayesBinaryRisk_le_min (μ ν : Measure 𝒳) (hp : p ≤ 1) :
    bayesBinaryRisk μ ν p hp ≤ min p (1 - p) := by
  sorry

lemma bayesBinaryRisk_symm (μ ν : Measure 𝒳) (hp : p ≤ 1) :
    bayesBinaryRisk μ ν p hp = bayesBinaryRisk ν μ (1 - p) tsub_le_self := by
  sorry

end ProbabilityTheory

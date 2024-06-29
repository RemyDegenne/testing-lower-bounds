/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Testing.Risk
import TestingLowerBounds.MeasureCompProd
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import TestingLowerBounds.BayesInv

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

section TwoHypKernel

/-- The kernel that sends `false` to `μ` and `true` to `ν`. -/
def twoHypKernel (μ ν : Measure 𝒳) : kernel Bool 𝒳 where
  val := fun b ↦ bif b then ν else μ
  property := measurable_discrete _

@[simp] lemma twoHypKernel_true : twoHypKernel μ ν true = ν := rfl

@[simp] lemma twoHypKernel_false : twoHypKernel μ ν false = μ := rfl

@[simp] lemma twoHypKernel_apply (b : Bool) : twoHypKernel μ ν b = bif b then ν else μ := rfl

instance [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteKernel (twoHypKernel μ ν) :=
  ⟨max (μ Set.univ) (ν Set.univ), max_lt (measure_lt_top _ _) (measure_lt_top _ _),
    fun b ↦ by cases b <;> simp⟩

instance [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsMarkovKernel (twoHypKernel μ ν) := by
  constructor
  intro b
  cases b
  · simp only [twoHypKernel_apply, cond_false]
    infer_instance
  · simp only [twoHypKernel_apply, cond_true]
    infer_instance

@[simp]
lemma comp_twoHypKernel (κ : kernel 𝒳 𝒴) :
    κ ∘ₖ (twoHypKernel μ ν) = twoHypKernel (μ ∘ₘ κ) (ν ∘ₘ κ) := by
  ext b : 1
  rw [kernel.comp_apply]
  cases b with
  | false => simp
  | true => simp

lemma measure_comp_twoHypKernel (μ ν : Measure 𝒳) (π : Measure Bool) :
    π ∘ₘ twoHypKernel μ ν = π {true} • ν + π {false} • μ := by
  ext s hs
  rw [Measure.bind_apply hs (kernel.measurable _)]
  simp only [twoHypKernel_apply, lintegral_fintype, Fintype.univ_bool, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, cond_true, Finset.sum_singleton,
    cond_false, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1 <;> rw [mul_comm]

lemma sum_smul_rnDeriv_twoHypKernel (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    (π {true} • ν.rnDeriv (π ∘ₘ twoHypKernel μ ν) + π {false} • (μ.rnDeriv (π ∘ₘ twoHypKernel μ ν)))
      =ᵐ[π ∘ₘ ⇑(twoHypKernel μ ν)] 1 := by
  have h1 := Measure.rnDeriv_smul_left_of_ne_top ν (π ∘ₘ twoHypKernel μ ν)
    (measure_ne_top π {true})
  have h2 := Measure.rnDeriv_smul_left_of_ne_top μ (π ∘ₘ twoHypKernel μ ν)
    (measure_ne_top π {false})
  have : IsFiniteMeasure (π {true} • ν) := ν.smul_finite (measure_ne_top _ _)
  have : IsFiniteMeasure (π {false} • μ) := μ.smul_finite (measure_ne_top _ _)
  have h3 := Measure.rnDeriv_add (π {true} • ν) (π {false} • μ) (π ∘ₘ twoHypKernel μ ν)
  have h4 := Measure.rnDeriv_self (π ∘ₘ twoHypKernel μ ν)
  filter_upwards [h1, h2, h3, h4] with a h1 h2 h3 h4
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h1 h2 h3 h4 ⊢
  rw [← h1, ← h2, ← h3, ← measure_comp_twoHypKernel, h4]

lemma sum_smul_rnDeriv_twoHypKernel' (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂(π ∘ₘ ⇑(twoHypKernel μ ν)), π {true} * ν.rnDeriv (π ∘ₘ twoHypKernel μ ν) x
      + π {false} * (μ.rnDeriv (π ∘ₘ twoHypKernel μ ν)) x = 1 := by
  filter_upwards [sum_smul_rnDeriv_twoHypKernel μ ν π] with x hx
  simpa using hx

noncomputable
def twoHypKernelInv (μ ν : Measure 𝒳) (π : Measure Bool) :
    kernel 𝒳 Bool where
  val x :=
    if π {true} * ν.rnDeriv (π ∘ₘ twoHypKernel μ ν) x
      + π {false} * (μ.rnDeriv (π ∘ₘ twoHypKernel μ ν)) x = 1
    then (π {true} * ν.rnDeriv (π ∘ₘ twoHypKernel μ ν) x) • Measure.dirac true
      + (π {false} * μ.rnDeriv (π ∘ₘ twoHypKernel μ ν) x) • Measure.dirac false
    else Measure.dirac true
  property := by
    refine Measurable.ite ?_ ?_ measurable_const
    · refine measurableSet_preimage ?_ (measurableSet_singleton _)
      exact ((Measure.measurable_rnDeriv _ _).const_mul _).add
        ((Measure.measurable_rnDeriv _ _).const_mul _)
    refine Measure.measurable_of_measurable_coe _ (fun s _ ↦ ?_)
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      MeasurableSpace.measurableSet_top, Measure.dirac_apply', smul_eq_mul]
    exact ((measurable_const.mul (Measure.measurable_rnDeriv _ _)).mul measurable_const).add
      ((measurable_const.mul (Measure.measurable_rnDeriv _ _)).mul measurable_const)

lemma twoHypKernelInv_apply (μ ν : Measure 𝒳) (π : Measure Bool) (x : 𝒳) :
    twoHypKernelInv μ ν π x
      = if π {true} * ν.rnDeriv (π ∘ₘ twoHypKernel μ ν) x
          + π {false} * (μ.rnDeriv (π ∘ₘ twoHypKernel μ ν)) x = 1
        then (π {true} * ν.rnDeriv (π ∘ₘ twoHypKernel μ ν) x) • Measure.dirac true
          + (π {false} * μ.rnDeriv (π ∘ₘ twoHypKernel μ ν) x) • Measure.dirac false
        else Measure.dirac true := rfl

lemma twoHypKernelInv_apply_ae (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂(π ∘ₘ ⇑(twoHypKernel μ ν)), twoHypKernelInv μ ν π x
      = (π {true} * ν.rnDeriv (π ∘ₘ twoHypKernel μ ν) x) • Measure.dirac true
        + (π {false} * μ.rnDeriv (π ∘ₘ twoHypKernel μ ν) x) • Measure.dirac false := by
  filter_upwards [sum_smul_rnDeriv_twoHypKernel' μ ν π] with x hx
  rw [twoHypKernelInv_apply, if_pos hx]

lemma twoHypKernelInv_apply' (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] (s : Set Bool) :
    ∀ᵐ x ∂(π ∘ₘ ⇑(twoHypKernel μ ν)), twoHypKernelInv μ ν π x s
      = π {true} * ν.rnDeriv (π ∘ₘ twoHypKernel μ ν) x * s.indicator 1 true
        + π {false} * μ.rnDeriv (π ∘ₘ twoHypKernel μ ν) x * s.indicator 1 false := by
  filter_upwards [twoHypKernelInv_apply_ae μ ν π] with x hx
  rw [hx]
  simp

instance (π : Measure Bool) [IsFiniteMeasure π] : IsMarkovKernel (twoHypKernelInv μ ν π) := by
  constructor
  intro x
  rw [twoHypKernelInv_apply]
  split_ifs with h
  · constructor
    simp [h]
  · infer_instance

lemma bayesInv_twoHypKernel (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ((twoHypKernel μ ν)†π) =ᵐ[π ∘ₘ twoHypKernel μ ν] twoHypKernelInv μ ν π := by
  symm
  refine eq_bayesInv_of_compProd_eq _ ?_
  ext s hs
  rw [Measure.map_apply measurable_swap hs, Measure.compProd_apply, Measure.compProd_apply,
    Measure.lintegral_bind (kernel.measurable _)]
  rotate_left
  · exact kernel.measurable_kernel_prod_mk_left hs
  · exact measurable_swap hs
  · exact hs
  simp only [twoHypKernel_apply]
  congr with b
  cases b
  · simp only [cond_false]
    sorry
  · simp only [cond_true]
    sorry

end TwoHypKernel

section SimpleBinaryHypTest

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

end SimpleBinaryHypTest

/-- The Bayes risk of simple binary hypothesis testing with respect to a prior. -/
noncomputable
def bayesBinaryRisk (μ ν : Measure 𝒳) (π : Measure Bool) : ℝ≥0∞ :=
  bayesRiskPrior (simpleBinaryHypTest μ ν) π

lemma bayesBinaryRisk_eq (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π
      = ⨅ (κ : kernel 𝒳 Bool) (_ : IsMarkovKernel κ),
        π {true} * (ν ∘ₘ κ) {false} + π {false} * (μ ∘ₘ κ) {true} := by
  rw [bayesBinaryRisk, bayesRiskPrior]
  congr with κ
  congr with _
  rw [bayesianRisk, lintegral_fintype, mul_comm (π {false}), mul_comm (π {true})]
  simp

/-- **Data processing inequality** for the Bayes binary risk. -/
lemma bayesBinaryRisk_le_bayesBinaryRisk_comp (μ ν : Measure 𝒳) (π : Measure Bool)
    (η : kernel 𝒳 𝒳') [IsMarkovKernel η] :
    bayesBinaryRisk μ ν π ≤ bayesBinaryRisk (μ ∘ₘ η) (ν ∘ₘ η) π :=
  (bayesRiskPrior_le_bayesRiskPrior_comp _ _ η).trans_eq (by simp [bayesBinaryRisk])

lemma bayesBinaryRisk_self (μ : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ μ π = min (π {true}) (π {false}) * μ Set.univ := by
  rw [bayesBinaryRisk_eq]
  sorry

lemma bayesBinaryRisk_le_min (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π ≤ min (π {true} * μ Set.univ) (π {false} * ν Set.univ) := by
  sorry

lemma bayesBinaryRisk_dirac (a b : ℝ≥0∞) (x : 𝒳) (π : Measure Bool) :
    bayesBinaryRisk (a • Measure.dirac x) (b • Measure.dirac x) π
      = min (π {true} * b) (π {false} * a) := by
  rw [bayesBinaryRisk_eq]
  have (κ : kernel 𝒳 Bool) [IsMarkovKernel κ] :
      π {true} * ((b • Measure.dirac x) ∘ₘ κ) {false}
        + π {false} * ((a • Measure.dirac x) ∘ₘ κ) {true}
      = (π {true} * b) * κ x {false} + (π {false} * a) * κ x {true} := by
    have (b : ℝ≥0∞) : (b • Measure.dirac x) ∘ₘ κ = b • κ x := by
      ext s hs
      simp only [Measure.bind_apply hs (kernel.measurable _), lintegral_smul_measure,
        Measure.smul_apply, smul_eq_mul]
      rw [lintegral_dirac']
      exact kernel.measurable_coe _ hs
    simp_rw [this]
    simp only [Measure.smul_apply, smul_eq_mul, mul_assoc]
  simp_rw [this]
  sorry

end ProbabilityTheory

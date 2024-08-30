/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.ForMathlib.MaxMinEqAbs
import TestingLowerBounds.Testing.Risk
import TestingLowerBounds.Testing.BoolMeasure
import Mathlib.MeasureTheory.Order.Group.Lattice

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
def twoHypKernel (μ ν : Measure 𝒳) : Kernel Bool 𝒳 where
  toFun := fun b ↦ bif b then ν else μ
  measurable' := measurable_discrete _

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

lemma Kernel_bool_eq_twoHypKernel (κ : Kernel Bool 𝒳) :
    κ = twoHypKernel (κ false) (κ true) := by
  ext (_ | _) <;> simp

@[simp]
lemma comp_twoHypKernel (κ : Kernel 𝒳 𝒴) :
    κ ∘ₖ (twoHypKernel μ ν) = twoHypKernel (κ ∘ₘ μ) (κ ∘ₘ ν) := by
  ext b : 1
  rw [Kernel.comp_apply]
  cases b with
  | false => simp
  | true => simp

lemma measure_comp_twoHypKernel (μ ν : Measure 𝒳) (π : Measure Bool) :
    twoHypKernel μ ν ∘ₘ π = π {true} • ν + π {false} • μ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.measurable _)]
  simp only [twoHypKernel_apply, lintegral_fintype, Fintype.univ_bool, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, cond_true, Finset.sum_singleton,
    cond_false, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1 <;> rw [mul_comm]

lemma absolutelyContinuous_measure_comp_twoHypKernel_left (μ ν : Measure 𝒳)
    {π : Measure Bool} (hπ : π {false} ≠ 0) :
    μ ≪ twoHypKernel μ ν ∘ₘ π :=
  measure_comp_twoHypKernel _ _ _ ▸ add_comm _ (π {true} • ν) ▸
    (Measure.absolutelyContinuous_smul hπ).add_right _

lemma absolutelyContinuous_measure_comp_twoHypKernel_right (μ ν : Measure 𝒳)
    {π : Measure Bool} (hπ : π {true} ≠ 0) :
    ν ≪ twoHypKernel μ ν ∘ₘ π :=
  measure_comp_twoHypKernel _ _ _ ▸ (Measure.absolutelyContinuous_smul hπ).add_right _

lemma sum_smul_rnDeriv_twoHypKernel (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    (π {true} • ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) + π {false} • (μ.rnDeriv (twoHypKernel μ ν ∘ₘ π)))
      =ᵐ[twoHypKernel μ ν ∘ₘ π] 1 := by
  have h1 := Measure.rnDeriv_smul_left_of_ne_top ν (twoHypKernel μ ν ∘ₘ π)
    (measure_ne_top π {true})
  have h2 := Measure.rnDeriv_smul_left_of_ne_top μ (twoHypKernel μ ν ∘ₘ π)
    (measure_ne_top π {false})
  have : IsFiniteMeasure (π {true} • ν) := ν.smul_finite (measure_ne_top _ _)
  have : IsFiniteMeasure (π {false} • μ) := μ.smul_finite (measure_ne_top _ _)
  have h3 := Measure.rnDeriv_add (π {true} • ν) (π {false} • μ) (twoHypKernel μ ν ∘ₘ π)
  have h4 := Measure.rnDeriv_self (twoHypKernel μ ν ∘ₘ π)
  filter_upwards [h1, h2, h3, h4] with a h1 h2 h3 h4
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h1 h2 h3 h4 ⊢
  rw [← h1, ← h2, ← h3, ← measure_comp_twoHypKernel, h4]

lemma sum_smul_rnDeriv_twoHypKernel' (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂(twoHypKernel μ ν ∘ₘ π), π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x
      + π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x = 1 := by
  filter_upwards [sum_smul_rnDeriv_twoHypKernel μ ν π] with x hx
  simpa using hx

/-- The kernel from `𝒳` to `Bool` defined by
`x ↦ (π₀ * ∂μ/∂(twoHypKernel μ ν ∘ₘ π) x + π₁ * ∂ν/∂(twoHypKernel μ ν ∘ₘ π) x)`.
It is the Bayesian inverse of `twoHypKernel μ ν` with respect to `π`
(see `bayesInv_twoHypKernel`). -/
noncomputable
def twoHypKernelInv (μ ν : Measure 𝒳) (π : Measure Bool) : Kernel 𝒳 Bool where
  toFun x :=
    if π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x
      + π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x = 1
    then (π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x) • Measure.dirac true
      + (π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x) • Measure.dirac false
    else Measure.dirac true
  measurable' := by
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
      = if π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x
          + π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x = 1
        then (π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x) • Measure.dirac true
          + (π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x) • Measure.dirac false
        else Measure.dirac true := rfl

lemma twoHypKernelInv_apply_ae (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂(twoHypKernel μ ν ∘ₘ π), twoHypKernelInv μ ν π x
      = (π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x) • Measure.dirac true
        + (π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x) • Measure.dirac false := by
  filter_upwards [sum_smul_rnDeriv_twoHypKernel' μ ν π] with x hx
  rw [twoHypKernelInv_apply, if_pos hx]

lemma twoHypKernelInv_apply' (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] (s : Set Bool) :
    ∀ᵐ x ∂(twoHypKernel μ ν ∘ₘ π), twoHypKernelInv μ ν π x s
      = π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x * s.indicator 1 true
        + π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x * s.indicator 1 false := by
  filter_upwards [twoHypKernelInv_apply_ae μ ν π] with x hx
  rw [hx]
  simp

lemma twoHypKernelInv_apply_false (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂(twoHypKernel μ ν ∘ₘ π),
      twoHypKernelInv μ ν π x {false} =  π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x := by
  filter_upwards [twoHypKernelInv_apply_ae μ ν π] with x hx
  simp [hx]

lemma twoHypKernelInv_apply_true (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ∀ᵐ x ∂(twoHypKernel μ ν ∘ₘ π),
      twoHypKernelInv μ ν π x {true} = π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x := by
  filter_upwards [twoHypKernelInv_apply_ae μ ν π] with x hx
  simp [hx]

instance (π : Measure Bool) : IsMarkovKernel (twoHypKernelInv μ ν π) := by
  constructor
  intro x
  rw [twoHypKernelInv_apply]
  split_ifs with h
  · constructor
    simp [h]
  · infer_instance

/- The finiteness hypothesis for μ should not be needed, but otherwise I dont know how to handle
the 3rd case, where I have the complement.
We still need some hp, the right one is probably SigmaFinite. For SFinite ones there is
a counterexample, see the comment above `Measure.prod_eq`.

TODO: generalize this lemma to SigmaFinite measures, there are 2 ways to do it,
one is to try and generalize this proof (for this it may be useful to try and apply the lemma used
in the proof of `Measure.prod_eq`), the other is to use this as an auxiliary lemma and prove
the result for SigmaFinite measures using this one (we can restrict the mesaure to the set
where it is finite and then use this lemma).
I'm not sure which way is better.
-/
lemma measure_prod_ext {μ ν : Measure (𝒳 × 𝒴)} [IsFiniteMeasure μ]
    (h : ∀ (A : Set 𝒳) (_ : MeasurableSet A) (B : Set 𝒴) (_ : MeasurableSet B),
      μ (A ×ˢ B) = ν (A ×ˢ B)) :
    μ = ν := by
  ext s hs
  apply MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod _ _ _ _ hs
  · simp_rw [measure_empty]
  · exact fun t ⟨A, hA, B, hB, ht⟩ ↦ ht ▸ h A hA B hB
  · intro t ht h_eq
    rw [measure_compl ht (measure_ne_top μ t), measure_compl ht (h_eq ▸ measure_ne_top μ t), h_eq,
      ← Set.univ_prod_univ, ← h Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ]
  · intro A h_disj h_meas h_eq
    simp_rw [measure_iUnion h_disj h_meas, h_eq]

lemma bayesInv_twoHypKernel (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    ((twoHypKernel μ ν)†π) =ᵐ[twoHypKernel μ ν ∘ₘ π] twoHypKernelInv μ ν π := by
  symm
  refine eq_bayesInv_of_compProd_eq _ (measure_prod_ext fun A hA B hB ↦ ?_)
  obtain (rfl | rfl | rfl | rfl) := Bool.cases_set_bool B
  · simp
  · rw [Measure.compProd_apply_prod hA hB, Measure.map_apply measurable_swap (hA.prod hB),
      Set.preimage_swap_prod, Measure.compProd_apply_prod hB hA, lintegral_singleton,
      twoHypKernel_apply, cond_true, setLIntegral_congr_fun hA _]
    rotate_left
    · exact fun x ↦ π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x
    · filter_upwards [twoHypKernelInv_apply' μ ν π {true}] with x hx
      simp [hx]
    simp_rw [mul_comm (π {true})]
    by_cases h_zero : π {true} = 0
    · simp [h_zero]
    rw [setLIntegral_rnDeriv_mul (absolutelyContinuous_measure_comp_twoHypKernel_right μ ν h_zero)
      aemeasurable_const hA]
    simp [mul_comm]
  · rw [Measure.compProd_apply_prod hA hB, Measure.map_apply measurable_swap (hA.prod hB),
      Set.preimage_swap_prod, Measure.compProd_apply_prod hB hA, lintegral_singleton,
      twoHypKernel_apply, cond_false, setLIntegral_congr_fun hA _]
    rotate_left
    · exact fun x ↦ π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x
    · filter_upwards [twoHypKernelInv_apply' μ ν π {false}] with x hx
      simp [hx]
    simp_rw [mul_comm (π {false})]
    by_cases h_zero : π {false} = 0
    · simp [h_zero]
    rw [setLIntegral_rnDeriv_mul (absolutelyContinuous_measure_comp_twoHypKernel_left μ ν h_zero)
      aemeasurable_const hA]
    simp [mul_comm]
  · rw [Measure.compProd_apply_prod hA hB, Measure.map_apply measurable_swap (hA.prod hB),
      Set.preimage_swap_prod, Measure.compProd_apply_prod hB hA,
      Bool.lintegral_bool, twoHypKernel_apply, twoHypKernel_apply, cond_false, cond_true,
      Set.pair_comm, ← Bool.univ_eq]
    simp only [measure_univ, lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
      Set.univ_inter, one_mul, Measure.restrict_univ]
    rw [Measure.bind_apply hA (by exact fun _ _ ↦ hB), Bool.lintegral_bool]
    simp

lemma bayesRiskPrior_eq_of_hasGenBayesEstimator_binary (E : estimationProblem Bool Bool Bool)
    (P : Kernel Bool 𝒳) [IsFiniteKernel P] (π : Measure Bool) [IsFiniteMeasure π]
    [h : HasGenBayesEstimator E P π] :
    bayesRiskPrior E P π
      = ∫⁻ x, ⨅ z, π {true} * (P true).rnDeriv (P ∘ₘ π) x * E.ℓ (E.y true, z)
        + π {false} * (P false).rnDeriv (P ∘ₘ π) x * E.ℓ (E.y false, z) ∂(P ∘ₘ π) := by
  simp_rw [bayesRiskPrior_eq_of_hasGenBayesEstimator]
  have h1 := bayesInv_twoHypKernel (P false) (P true) π
  have h2 : P = twoHypKernel (P false) (P true) := Kernel_bool_eq_twoHypKernel P
  have h3 : (P†π) = twoHypKernel (P false) (P true)†π := by congr
  nth_rw 1 [h2]
  nth_rw 4 [h2]
  simp_rw [h3]
  apply lintegral_congr_ae
  filter_upwards [h1, twoHypKernelInv_apply_false (P false) (P true) π,
    twoHypKernelInv_apply_true (P false) (P true) π] with x hx h_false h_true
  congr with z
  rw [Bool.lintegral_bool, hx, h_false, h_true, ← h2]
  ring_nf

end TwoHypKernel

section SimpleBinaryHypTest

/-- Simple binary hypothesis testing problem: a testing problem where `Θ = 𝒴 = 𝒵 = {0,1}`, `y` is
the identity and the loss is `ℓ(y₀, z) = 𝕀{y₀ ≠ z}`. -/
@[simps]
noncomputable
def simpleBinaryHypTest : estimationProblem Bool Bool Bool where
  y := id
  y_meas := measurable_id
  ℓ := fun (y, z) ↦ if y = z then 0 else 1
  ℓ_meas := measurable_discrete _

@[simp]
lemma risk_simpleBinaryHypTest_true (μ ν : Measure 𝒳) (κ : Kernel 𝒳 Bool) :
    risk simpleBinaryHypTest (twoHypKernel μ ν) κ true = (κ ∘ₘ ν) {false} := by
  simp only [risk, simpleBinaryHypTest, comp_twoHypKernel, twoHypKernel_apply, cond_true, id_eq,
    Bool.true_eq, MeasurableSpace.measurableSet_top]
  calc ∫⁻ z, if z = true then 0 else 1 ∂(κ ∘ₘ ν)
  _ = ∫⁻ z, Set.indicator {false} (fun _ ↦ 1) z ∂(κ ∘ₘ ν) := by
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
  _ = (κ ∘ₘ ν) {false} := lintegral_indicator_one (measurableSet_singleton _)

@[simp]
lemma risk_simpleBinaryHypTest_false (μ ν : Measure 𝒳) (κ : Kernel 𝒳 Bool) :
    risk simpleBinaryHypTest (twoHypKernel μ ν) κ false = (κ ∘ₘ μ) {true} := by
  simp only [risk, simpleBinaryHypTest, comp_twoHypKernel, twoHypKernel_apply, cond_false, id_eq,
    Bool.false_eq, MeasurableSpace.measurableSet_top]
  calc ∫⁻ z, if z = false then 0 else 1 ∂(κ ∘ₘ μ)
  _ = ∫⁻ z, Set.indicator {true} (fun _ ↦ 1) z ∂(κ ∘ₘ μ) := by
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
  _ = (κ ∘ₘ μ) {true} := lintegral_indicator_one (measurableSet_singleton _)

/-- The function `x ↦ 𝕀{π₀ * ∂μ/∂(twoHypKernel μ ν ∘ₘ π) x ≤ π₁ * ∂ν/∂(twoHypKernel μ ν ∘ₘ π) x}`.
It is a Generalized Bayes estimator for the simple binary hypothesis testing problem. -/
noncomputable
def binaryGenBayesEstimator (μ ν : Measure 𝒳) (π : Measure Bool) : 𝒳 → Bool :=
  let E : Set 𝒳 := {x | π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x
    ≤ π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x}
  fun x ↦ Bool.ofNat (E.indicator 1 x)

lemma binaryGenBayesEstimator_isGenBayesEstimator (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    IsGenBayesEstimator simpleBinaryHypTest (twoHypKernel μ ν)
      (binaryGenBayesEstimator μ ν π) π := by
  refine ⟨?_, ?_⟩
  · simp_rw [binaryGenBayesEstimator]
    refine ((measurable_discrete _).comp' (measurable_one.indicator (measurableSet_le ?_ ?_)))
      <;> fun_prop
  · filter_upwards [bayesInv_twoHypKernel μ ν π, twoHypKernelInv_apply' μ ν π {true},
      twoHypKernelInv_apply' μ ν π {false}] with x hx h_true h_false
    refine le_antisymm (le_iInf fun b ↦ ?_) (iInf_le _ _)
    cases b <;> by_cases
      π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x ≤ π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x
      <;> simp_all [Bool.lintegral_bool, binaryGenBayesEstimator, Bool.ofNat, -not_le, le_of_not_ge]

noncomputable instance (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    HasGenBayesEstimator simpleBinaryHypTest (twoHypKernel μ ν) π :=
  ⟨binaryGenBayesEstimator μ ν π, binaryGenBayesEstimator_isGenBayesEstimator μ ν π⟩

end SimpleBinaryHypTest

/-- The Bayes risk of simple binary hypothesis testing with respect to a prior. -/
noncomputable
def bayesBinaryRisk (μ ν : Measure 𝒳) (π : Measure Bool) : ℝ≥0∞ :=
  bayesRiskPrior simpleBinaryHypTest (twoHypKernel μ ν) π

lemma bayesBinaryRisk_eq (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π
      = ⨅ (κ : Kernel 𝒳 Bool) (_ : IsMarkovKernel κ),
        π {true} * (κ ∘ₘ ν) {false} + π {false} * (κ ∘ₘ μ) {true} := by
  rw [bayesBinaryRisk, bayesRiskPrior]
  congr with κ
  congr with _
  rw [bayesianRisk, lintegral_fintype, mul_comm (π {false}), mul_comm (π {true})]
  simp

variable {π : Measure Bool}

/-- `B (a•μ, b•ν; π) = B (μ, ν; (a*π₀, b*π₁)).` -/
lemma bayesBinaryRisk_smul_smul (μ ν : Measure 𝒳) (π : Measure Bool) (a b : ℝ≥0∞) :
    bayesBinaryRisk (a • μ) (b • ν) π
      = bayesBinaryRisk μ ν (π.withDensity (fun x ↦ bif x then b else a)) := by
  simp [bayesBinaryRisk_eq, Measure.comp_smul_left, lintegral_dirac, mul_assoc]

lemma bayesBinaryRisk_eq_bayesBinaryRisk_one_one (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π
      = bayesBinaryRisk (π {false} • μ) (π {true} • ν) (Bool.boolMeasure 1 1) := by
  rw [bayesBinaryRisk_smul_smul, Bool.measure_eq_boolMeasure π, Bool.boolMeasure_withDensity]
  simp

/-- **Data processing inequality** for the Bayes binary risk. -/
lemma bayesBinaryRisk_le_bayesBinaryRisk_comp (μ ν : Measure 𝒳) (π : Measure Bool)
    (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] :
    bayesBinaryRisk μ ν π ≤ bayesBinaryRisk (η ∘ₘ μ) (η ∘ₘ ν) π :=
  (bayesRiskPrior_le_bayesRiskPrior_comp _ _ _ η).trans_eq (by simp [bayesBinaryRisk])

lemma nonempty_subtype_isMarkovKernel_of_nonempty {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳}
    {𝒴 : Type*} {m𝒴 : MeasurableSpace 𝒴} [Nonempty 𝒴] :
    Nonempty (Subtype (@IsMarkovKernel 𝒳 𝒴 m𝒳 m𝒴)) := by
  simp only [nonempty_subtype, Subtype.exists]
  let y : 𝒴 := Classical.ofNonempty
  exact ⟨Kernel.const _ (Measure.dirac y), inferInstance⟩

@[simp]
lemma bayesBinaryRisk_self (μ : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ μ π = min (π {false}) (π {true}) * μ Set.univ := by
  rw [bayesBinaryRisk_eq]
  refine le_antisymm ?_ ?_
  · let η : Kernel 𝒳 Bool :=
      if π {true} ≤ π {false} then (Kernel.const 𝒳 (Measure.dirac false))
        else (Kernel.const 𝒳 (Measure.dirac true))
    refine iInf_le_of_le η ?_
    simp_rw [η]
    convert iInf_le _ ?_ using 1
    · split_ifs with h <;> simp [le_of_not_ge, h]
    · split_ifs <;> infer_instance
  · calc
      _ ≥ ⨅ κ, ⨅ (_ : IsMarkovKernel κ), min (π {false}) (π {true}) * (κ ∘ₘ μ) {false}
          + min (π {false}) (π {true}) * (κ ∘ₘ μ) {true} := by
        gcongr <;> simp
      _ = ⨅ κ, ⨅ (_ : IsMarkovKernel κ), min (π {false}) (π {true}) * μ Set.univ := by
        simp_rw [← mul_add, ← measure_union (show Disjoint {false} {true} from by simp)
          (by trivial), (set_fintype_card_eq_univ_iff ({false} ∪ {true})).mp rfl,
          Measure.comp_apply_univ]
        rfl
      _ = _ := by
        rw [iInf_subtype']
        convert iInf_const
        exact nonempty_subtype_isMarkovKernel_of_nonempty

lemma bayesBinaryRisk_dirac (a b : ℝ≥0∞) (x : 𝒳) (π : Measure Bool) :
    bayesBinaryRisk (a • Measure.dirac x) (b • Measure.dirac x) π
      = min (π {false} * a) (π {true} * b) := by
  rw [bayesBinaryRisk_smul_smul, bayesBinaryRisk_self]
  simp [lintegral_dirac]

lemma bayesBinaryRisk_le_min (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π ≤ min (π {false} * μ Set.univ) (π {true} * ν Set.univ) := by
  convert bayesBinaryRisk_le_bayesBinaryRisk_comp μ ν π (Kernel.discard 𝒳)
  simp_rw [Measure.comp_discard, bayesBinaryRisk_dirac]

@[simp] lemma bayesBinaryRisk_zero_left : bayesBinaryRisk 0 ν π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le'

@[simp] lemma bayesBinaryRisk_zero_right : bayesBinaryRisk μ 0 π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le'

@[simp] lemma bayesBinaryRisk_zero_prior : bayesBinaryRisk μ ν 0 = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le'

lemma bayesBinaryRisk_ne_top (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π ≠ ∞ := by
  refine lt_top_iff_ne_top.mp ((bayesBinaryRisk_le_min μ ν π).trans_lt ?_)
  exact min_lt_iff.mpr <| Or.inl <| ENNReal.mul_lt_top (measure_lt_top π _) (measure_lt_top μ _)

lemma bayesBinaryRisk_of_measure_true_eq_zero (μ ν : Measure 𝒳) (hπ : π {true} = 0) :
    bayesBinaryRisk μ ν π = 0 := by
  refine le_antisymm ?_ (zero_le _)
  convert bayesBinaryRisk_le_min μ ν π
  simp [hπ]

lemma bayesBinaryRisk_of_measure_false_eq_zero (μ ν : Measure 𝒳) (hπ : π {false} = 0) :
    bayesBinaryRisk μ ν π = 0 := by
  refine le_antisymm ?_ (zero_le _)
  convert bayesBinaryRisk_le_min μ ν π
  simp [hπ]

lemma bayesBinaryRisk_symm (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π = bayesBinaryRisk ν μ (π.map Bool.not) := by
  have : (Bool.not ⁻¹' {true}) = {false} := by ext x; simp
  have h1 : (Measure.map Bool.not π) {true} = π {false} := by
    rw [Measure.map_apply (by exact fun _ a ↦ a) (by trivial), this]
  have : (Bool.not ⁻¹' {false}) = {true} := by ext x; simp
  have h2 : (Measure.map Bool.not π) {false} = π {true} := by
    rw [Measure.map_apply (by exact fun _ a ↦ a) (by trivial), this]
  simp_rw [bayesBinaryRisk_eq, h1, h2, add_comm, iInf_subtype']
  -- from this point on the proof is basically a change of variable inside the iInf,
  -- to do this I define an equivalence between `Subtype IsMarkovKernel` and itself through
  -- the `Bool.not` operation, maybe it can be shortened or something can be separated as
  -- a different lemma, but I'm not sure how useful this would be
  let e : (Kernel 𝒳 Bool) ≃ (Kernel 𝒳 Bool) := by
    have h_id : Kernel.comap (Kernel.deterministic Bool.not (fun _ a ↦ a)) Bool.not (fun _ a ↦ a)
        = Kernel.id := by
      ext x : 1
      simp_rw [Kernel.comap_apply, Kernel.deterministic_apply, Kernel.id_apply, Bool.not_not]
    refine ⟨fun κ ↦ (Kernel.deterministic Bool.not (fun _ a ↦ a)) ∘ₖ κ,
      fun κ ↦ (Kernel.deterministic Bool.not (fun _ a ↦ a)) ∘ₖ κ, fun κ ↦ ?_, fun κ ↦ ?_⟩ <;>
    · dsimp
      ext x : 1
      rw [← Kernel.comp_assoc, Kernel.comp_deterministic_eq_comap, h_id, Kernel.id_comp]
  let e' : (Subtype (@IsMarkovKernel 𝒳 Bool _ _)) ≃ (Subtype (@IsMarkovKernel 𝒳 Bool _ _)) := by
    refine ⟨fun ⟨κ, _⟩ ↦ ⟨e κ, ?_⟩, fun ⟨κ, _⟩ ↦ ⟨e.symm κ, ?_⟩, fun κ ↦ by simp, fun κ ↦ by simp⟩
      <;> simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, e] <;> infer_instance
  rw [← Equiv.iInf_comp e']
  congr with κ
  simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, MeasurableSpace.measurableSet_top, e', e]
  have h3 b : Set.indicator {true} (1 : Bool → ℝ≥0∞) b.not = Set.indicator {false} 1 b := by
    cases b <;> simp
  have h4 b : Set.indicator {false} (1 : Bool → ℝ≥0∞) b.not = Set.indicator {true} 1 b := by
    cases b <;> simp
  congr 2 <;>
  · rw [Measure.bind_apply (by trivial) (Kernel.measurable _),
      Measure.bind_apply (by trivial) (Kernel.measurable _)]
    congr with x
    rw [Kernel.comp_apply']
    simp only [Measure.dirac_apply' _ (show MeasurableSet {true} by trivial),
      Measure.dirac_apply' _ (show MeasurableSet {false} by trivial), Kernel.deterministic_apply]
    swap; trivial
    simp [h3, h4]

lemma bayesianRisk_binary_of_deterministic_indicator (μ ν : Measure 𝒳) (π : Measure Bool)
    {E : Set 𝒳} (hE : MeasurableSet E) :
    bayesianRisk simpleBinaryHypTest (twoHypKernel μ ν)
      (Kernel.deterministic (fun x ↦ Bool.ofNat (E.indicator 1 x))
        ((measurable_discrete _).comp' (measurable_one.indicator hE))) π
      = π {false} * μ E + π {true} * ν Eᶜ := by
  have h_meas : Measurable fun x ↦ Bool.ofNat (E.indicator 1 x) :=
    (measurable_discrete _).comp' (measurable_one.indicator hE)
  have h1 : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {false} = Eᶜ := by
    ext; simp [Bool.ofNat]
  have h2 : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {true} = E := by
    ext; simp [Bool.ofNat]
  rw [bayesianRisk, Bool.lintegral_bool, mul_comm (π {false}), mul_comm (π {true})]
  simp only [risk_simpleBinaryHypTest_false, MeasurableSpace.measurableSet_top,
    risk_simpleBinaryHypTest_true]
  simp_rw [Measure.comp_deterministic_eq_map, Measure.map_apply h_meas trivial, h1, h2]

lemma bayesBinaryRisk_eq_iInf_measurableSet (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = ⨅ E, ⨅ (_ : MeasurableSet E), π {false} * μ E + π {true} * ν Eᶜ := by
  apply le_antisymm
  · simp_rw [le_iInf_iff, bayesBinaryRisk, bayesRiskPrior]
    intro E hE
    rw [← bayesianRisk_binary_of_deterministic_indicator _ _ _ hE]
    exact iInf_le_of_le _ (iInf_le _ (Kernel.isMarkovKernel_deterministic _))
  · let E := {x | π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x
      ≤ π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x}
    have hE : MeasurableSet E := measurableSet_le (by fun_prop) (by fun_prop)
    rw [bayesBinaryRisk, ← isBayesEstimator_of_isGenBayesEstimator
      (binaryGenBayesEstimator_isGenBayesEstimator μ ν π), IsGenBayesEstimator.Kernel]
    simp_rw [binaryGenBayesEstimator, bayesianRisk_binary_of_deterministic_indicator _ _ _ hE]
    exact iInf_le_of_le E (iInf_le _ hE)

lemma bayesBinaryRisk_eq_lintegral_min (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = ∫⁻ x, min (π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x)
      (π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x) ∂(twoHypKernel μ ν ∘ₘ π) := by
  simp_rw [bayesBinaryRisk, bayesRiskPrior_eq_of_hasGenBayesEstimator_binary, Bool.iInf_bool]
  simp [min_comm]

lemma toReal_bayesBinaryRisk_eq_integral_min (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    (bayesBinaryRisk μ ν π).toReal
      = ∫ x, min (π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x).toReal
        (π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x).toReal ∂(twoHypKernel μ ν ∘ₘ π) := by
  rw [bayesBinaryRisk_eq_lintegral_min, integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · filter_upwards with x; positivity
  · refine Measurable.aestronglyMeasurable <| Measurable.min ?_ ?_
      <;> exact Measure.measurable_rnDeriv _ _ |>.const_mul _ |>.ennreal_toNNReal |>.coe_nnreal_real
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_ne_top μ _, Measure.rnDeriv_ne_top ν _] with x hxμ hxν
  have : (π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x) ≠ ⊤ :=
    (ENNReal.mul_ne_top (measure_ne_top _ _) hxμ)
  have : (π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x) ≠ ⊤ :=
    (ENNReal.mul_ne_top (measure_ne_top _ _) hxν)
  rcases le_total (π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x)
    (π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x) with h | h
  all_goals
  · have h' := (ENNReal.toReal_le_toReal (by assumption) (by assumption)).mpr h
    simp only [h, h', min_eq_left, min_eq_right]
    exact (ENNReal.ofReal_toReal_eq_iff.mpr (by assumption)).symm

lemma toReal_bayesBinaryRisk_eq_integral_abs (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    (bayesBinaryRisk μ ν π).toReal
      = 2⁻¹ * (((twoHypKernel μ ν ∘ₘ π) Set.univ).toReal
        - ∫ x, |(π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x).toReal
          - (π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x).toReal| ∂(twoHypKernel μ ν ∘ₘ π)) := by
  simp_rw [toReal_bayesBinaryRisk_eq_integral_min, min_eq_add_sub_abs_sub, integral_mul_left]
  congr
  have hμ_int : Integrable (fun x ↦ (π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x).toReal)
      (twoHypKernel μ ν ∘ₘ π) := by
    simp_rw [ENNReal.toReal_mul]
    exact Integrable.const_mul Measure.integrable_toReal_rnDeriv _
  have hν_int : Integrable (fun x ↦ (π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x).toReal)
      (twoHypKernel μ ν ∘ₘ π) := by
    simp_rw [ENNReal.toReal_mul]
    exact Integrable.const_mul Measure.integrable_toReal_rnDeriv _
  have h_int_abs : Integrable (fun x ↦ |(π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x).toReal
      - (π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x).toReal|) (twoHypKernel μ ν ∘ₘ π) :=
    hμ_int.sub hν_int |>.abs
  rw [integral_sub (by exact hμ_int.add hν_int) h_int_abs, integral_add hμ_int hν_int]
  simp only [ENNReal.toReal_mul, MeasurableSet.univ, sub_left_inj, integral_mul_left]
  nth_rw 5 [measure_comp_twoHypKernel]
  calc
    _ = (π {false}).toReal * (μ Set.univ).toReal + (π {true}).toReal
        * ∫ (a : 𝒳), ((∂ν/∂twoHypKernel μ ν ∘ₘ π) a).toReal ∂(twoHypKernel μ ν ∘ₘ π) := by
      by_cases hπ_false : π {false} = 0
      · simp [hπ_false, bayesBinaryRisk_of_measure_false_eq_zero]
      rw [Measure.integral_toReal_rnDeriv
        (absolutelyContinuous_measure_comp_twoHypKernel_left μ ν hπ_false)]
    _ = (π {false}).toReal * (μ Set.univ).toReal + (π {true}).toReal * (ν Set.univ).toReal := by
      by_cases hπ_true : π {true} = 0
      · simp [hπ_true, bayesBinaryRisk_of_measure_true_eq_zero]
      rw [Measure.integral_toReal_rnDeriv
        (absolutelyContinuous_measure_comp_twoHypKernel_right μ ν hπ_true)]
    _ = _ := by
      simp_rw [add_comm, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _)
        (measure_ne_top _ _)) (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
        ENNReal.toReal_mul]

lemma bayesBinaryRisk_eq_lintegral_ennnorm (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = 2⁻¹ * (((twoHypKernel μ ν ∘ₘ π) Set.univ)
        - ∫⁻ x, ‖(π {false} * (∂μ/∂(twoHypKernel μ ν ∘ₘ π)) x).toReal
          - (π {true} * (∂ν/∂(twoHypKernel μ ν ∘ₘ π)) x).toReal‖₊ ∂(twoHypKernel μ ν ∘ₘ π)) := by
  rw [← ENNReal.ofReal_toReal (bayesBinaryRisk_ne_top μ ν π),
    toReal_bayesBinaryRisk_eq_integral_abs, ENNReal.ofReal_mul (inv_nonneg.mpr zero_le_two),
    ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat,
    ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_toReal (measure_ne_top _ _),
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal _
    (.of_forall fun _ ↦ by positivity)]
  swap
  · refine ⟨Measurable.aestronglyMeasurable (by fun_prop), ?_⟩
    simp_rw [HasFiniteIntegral, Real.nnnorm_abs]
    calc
      _ ≤ ∫⁻ a, ‖(π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) a).toReal‖₊ +
          ‖(π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) a).toReal‖₊ ∂(twoHypKernel μ ν ∘ₘ π) := by
        gcongr
        exact_mod_cast nnnorm_sub_le _ _
      _ = ∫⁻ a, ‖(π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) a).toReal‖₊ ∂(twoHypKernel μ ν ∘ₘ π) +
          ∫⁻ a, ‖(π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) a).toReal‖₊ ∂(twoHypKernel μ ν ∘ₘ π) :=
        lintegral_add_left (by fun_prop) _
      _ ≤ π {false} * ∫⁻ a, ‖((∂μ/∂twoHypKernel μ ν ∘ₘ π) a).toReal‖₊ ∂(twoHypKernel μ ν ∘ₘ π) +
          π {true} * ∫⁻ a, ‖((∂ν/∂twoHypKernel μ ν ∘ₘ π) a).toReal‖₊ ∂(twoHypKernel μ ν ∘ₘ π) := by
        simp_rw [ENNReal.toReal_mul, nnnorm_mul, ENNReal.coe_mul]
        rw [lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
        gcongr <;>
        · rw [Real.ennnorm_eq_ofReal_abs, ENNReal.abs_toReal]
          exact ENNReal.ofReal_toReal_le
      _ ≤ π {false} * ∫⁻ a, (∂μ/∂twoHypKernel μ ν ∘ₘ π) a ∂(twoHypKernel μ ν ∘ₘ π) +
          π {true} * ∫⁻ a, (∂ν/∂twoHypKernel μ ν ∘ₘ π) a ∂(twoHypKernel μ ν ∘ₘ π) := by
        gcongr <;>
        · rw [Real.ennnorm_eq_ofReal_abs, ENNReal.abs_toReal]
          exact ENNReal.ofReal_toReal_le
      _ = π {false} * μ Set.univ + π {true} * ν Set.univ := by
        congr 1
        · by_cases h_false : π {false} = 0
          · rw [h_false, zero_mul, zero_mul]
          rw [Measure.lintegral_rnDeriv
            (absolutelyContinuous_measure_comp_twoHypKernel_left μ ν h_false)]
        · by_cases h_true : π {true} = 0
          · rw [h_true, zero_mul, zero_mul]
          rw [Measure.lintegral_rnDeriv
            (absolutelyContinuous_measure_comp_twoHypKernel_right μ ν h_true)]
      _ < ⊤ :=
        ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _),
          ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)⟩
  simp_rw [Real.ennnorm_eq_ofReal_abs]

end ProbabilityTheory

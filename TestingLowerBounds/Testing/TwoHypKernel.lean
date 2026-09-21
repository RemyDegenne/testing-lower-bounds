/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Testing.BoolMeasure
import TestingLowerBounds.Testing.Risk

/-!
# Kernel with two values

-/

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝒳 𝒳' 𝒴 𝒵 : Type*} {mΘ : MeasurableSpace Θ} {m𝒳 : MeasurableSpace 𝒳}
  {m𝒳' : MeasurableSpace 𝒳'} {m𝒴 : MeasurableSpace 𝒴} {m𝒵 : MeasurableSpace 𝒵}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞}

/-- The kernel that sends `false` to `μ` and `true` to `ν`. -/
def twoHypKernel (μ ν : Measure 𝒳) : Kernel Bool 𝒳 where
  toFun := fun b ↦ bif b then ν else μ
  measurable' := .of_discrete

@[simp] lemma twoHypKernel_true : twoHypKernel μ ν true = ν := rfl

@[simp] lemma twoHypKernel_false : twoHypKernel μ ν false = μ := rfl

@[simp] lemma twoHypKernel_apply (b : Bool) : twoHypKernel μ ν b = bif b then ν else μ := rfl

instance [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteKernel (twoHypKernel μ ν) :=
  ⟨max (μ .univ) (ν .univ), max_lt (measure_lt_top _ _) (measure_lt_top _ _),
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
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
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
  have h1 := ν.rnDeriv_smul_left_of_ne_top (twoHypKernel μ ν ∘ₘ π)
    (measure_ne_top π {true})
  have h2 := μ.rnDeriv_smul_left_of_ne_top (twoHypKernel μ ν ∘ₘ π)
    (measure_ne_top π {false})
  have : IsFiniteMeasure (π {true} • ν) := ν.smul_finite (measure_ne_top _ _)
  have : IsFiniteMeasure (π {false} • μ) := μ.smul_finite (measure_ne_top _ _)
  have h3 := (π {true} • ν).rnDeriv_add  (π {false} • μ) (twoHypKernel μ ν ∘ₘ π)
  have h4 := (twoHypKernel μ ν ∘ₘ π).rnDeriv_self
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
      exact ((ν.measurable_rnDeriv _).const_mul _).add ((μ.measurable_rnDeriv _).const_mul _)
    refine Measure.measurable_of_measurable_coe _ (fun s _ ↦ ?_)
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      MeasurableSpace.measurableSet_top, Measure.dirac_apply', smul_eq_mul]
    exact ((measurable_const.mul (ν.measurable_rnDeriv _)).mul measurable_const).add
      ((measurable_const.mul (μ.measurable_rnDeriv _)).mul measurable_const)

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
  induction s, hs using MeasurableSpace.induction_on_inter generateFrom_prod.symm
    isPiSystem_prod with
  | empty => simp_rw [measure_empty]
  | basic t ht =>
    obtain ⟨A, hA, B, hB, rfl⟩ := ht
    exact h A hA B hB
  | compl t ht h_eq =>
    rw [measure_compl ht (measure_ne_top μ t), measure_compl ht (h_eq ▸ measure_ne_top μ t), h_eq,
      ← Set.univ_prod_univ, ← h _ .univ _ .univ]
  | iUnion A h_disj h_meas h_eq =>
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
      twoHypKernel_apply, cond_true, setLIntegral_congr_fun_ae hA _]
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
      twoHypKernel_apply, cond_false, setLIntegral_congr_fun_ae hA _]
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
    rw [Measure.bind_apply hA (twoHypKernel μ ν).measurable.aemeasurable, Bool.lintegral_bool]
    simp

lemma bayesRiskPrior_eq_of_hasGenBayesEstimator_binary {𝒴 𝒵 : Type*}
    [MeasurableSpace 𝒴] [MeasurableSpace 𝒵] (E : estimationProblem Bool 𝒴 𝒵)
    (P : Kernel Bool 𝒳) [IsFiniteKernel P] (π : Measure Bool) [IsFiniteMeasure π]
    [h : HasGenBayesEstimator E P π] :
    bayesRiskPrior E P π
      = ∫⁻ x, ⨅ z, π {true} * (P true).rnDeriv (P ∘ₘ π) x * E.ℓ (E.y true, z)
        + π {false} * (P false).rnDeriv (P ∘ₘ π) x * E.ℓ (E.y false, z) ∂(P ∘ₘ π) := by
  simp_rw [bayesRiskPrior_eq_of_hasGenBayesEstimator]
  have h1 := bayesInv_twoHypKernel (P false) (P true) π
  have h2 : P = twoHypKernel (P false) (P true) := Kernel_bool_eq_twoHypKernel P
  have h3 : (P†π) = twoHypKernel (P false) (P true)†π := by congr
  nth_rw 1 3 [h2]
  simp_rw [h3]
  apply lintegral_congr_ae
  filter_upwards [h1, twoHypKernelInv_apply_false (P false) (P true) π,
    twoHypKernelInv_apply_true (P false) (P true) π] with x hx h_false h_true
  congr with z
  rw [Bool.lintegral_bool, hx, h_false, h_true, ← h2]
  ring_nf

end ProbabilityTheory

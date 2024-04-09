/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import TestingLowerBounds.FDiv.CondFDiv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Kullback-Leibler divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open Real MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

section move_this

lemma integrable_rnDeriv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν)
    [SigmaFinite μ] {f : α → E} (hf : Integrable f μ) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal • f x) ν :=
  (integrable_rnDeriv_smul_iff hμν).mpr hf

end move_this

open Classical in
/-- Kullback-Leibler divergence between two measures. -/
noncomputable def kl (μ ν : Measure α) : EReal :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ then ↑(∫ x, llr μ ν x ∂μ) else ⊤

lemma kl_of_ac_of_integrable (h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) :
    kl μ ν = ∫ x, llr μ ν x ∂μ := if_pos ⟨h1, h2⟩

@[simp]
lemma kl_of_not_ac (h : ¬ μ ≪ ν) : kl μ ν = ⊤ := if_neg (not_and_of_not_left _ h)

@[simp]
lemma kl_of_not_integrable (h : ¬ Integrable (llr μ ν) μ) : kl μ ν = ⊤ :=
  if_neg (not_and_of_not_right _ h)

lemma integrable_rnDeriv_mul_log_iff [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal) ν
      ↔ Integrable (llr μ ν) μ :=
  integrable_rnDeriv_smul_iff hμν

lemma derivAtTop_mul_log : derivAtTop (fun x ↦ x * log x) = ⊤ := by
  rw [derivAtTop_eq_top_iff]
  refine (tendsto_congr' ?_).mp tendsto_log_atTop
  simp only [EventuallyEq, eventually_atTop, ge_iff_le]
  refine ⟨1, fun x hx ↦ ?_⟩
  rw [mul_div_cancel_left₀ _ (zero_lt_one.trans_le hx).ne']

lemma fDiv_mul_log_eq_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv (fun x ↦ x * log x) μ ν = ⊤ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ := by
  rw [fDiv_eq_top_iff]
  simp only [derivAtTop_mul_log, true_and]
  by_cases hμν : μ ≪ ν
  · simp [hμν, integrable_rnDeriv_mul_log_iff hμν]
  · simp [hμν]

lemma kl_eq_fDiv [SigmaFinite μ] [SigmaFinite ν] :
    kl μ ν = fDiv (fun x ↦ x * log x) μ ν := by
  classical
  by_cases hμν : μ ≪ ν
  swap; · rw [fDiv_of_not_ac derivAtTop_mul_log hμν, kl_of_not_ac hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [fDiv_of_derivAtTop_eq_top derivAtTop_mul_log, kl_of_ac_of_integrable hμν h_int,
      if_pos ⟨(integrable_rnDeriv_mul_log_iff hμν).mpr h_int, hμν⟩]
    simp_rw [← smul_eq_mul]
    rw [integral_rnDeriv_smul hμν]
    rfl
  · rw [kl_of_not_integrable h_int, fDiv_of_not_integrable]
    rwa [integrable_rnDeriv_mul_log_iff hμν]

@[simp]
lemma kl_self (μ : Measure α) [SigmaFinite μ] : kl μ μ = 0 := by
  rw [kl_eq_fDiv, fDiv_self (by norm_num)]

section kl_nonneg

lemma kl_ne_bot (μ ν : Measure α) : kl μ ν ≠ ⊥ := by
  rw [kl]
  split_ifs with h
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
  · norm_num

lemma kl_ge_mul_log' [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (μ Set.univ).toReal * log (μ Set.univ).toReal ≤ kl μ ν :=
  (le_fDiv_of_ac Real.convexOn_mul_log Real.continuous_mul_log.continuousOn hμν).trans_eq
    kl_eq_fDiv.symm

lemma kl_ge_mul_log (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ Set.univ).toReal * log ((μ Set.univ).toReal / (ν Set.univ).toReal) ≤ kl μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [h_int]
  rw [kl_of_ac_of_integrable hμν h_int]
  norm_cast
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    apply? says exact Measure.measure_univ_eq_zero.mp (hμν rfl)
  let ν' := (ν Set.univ)⁻¹ • ν
  have : IsProbabilityMeasure ν' := by
    constructor
    simp only [ν', Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ENNReal.mul_inv_cancel]
    · simp [hν]
    · exact measure_ne_top _ _
  have hμν' : μ ≪ ν' := by
    refine Measure.AbsolutelyContinuous.trans hμν (Measure.absolutelyContinuous_smul ?_)
    simp [measure_ne_top ν]
  have h := kl_ge_mul_log' hμν'
  rw [kl_of_ac_of_integrable hμν', integral_congr_ae (llr_smul_right hμν (ν Set.univ)⁻¹ _ _)] at h
  rotate_left
  · simp [measure_ne_top ν _]
  · simp [hν]
  · rw [integrable_congr (llr_smul_right hμν (ν Set.univ)⁻¹ _ _)]
    rotate_left
    · simp [measure_ne_top ν _]
    · simp [hν]
    exact h_int.sub (integrable_const _)
  norm_cast at h
  rw [integral_sub h_int (integrable_const _), integral_const, smul_eq_mul, le_sub_iff_add_le,
    ENNReal.toReal_inv, log_inv, mul_neg, ← sub_eq_add_neg] at h
  rwa [log_div, mul_sub]
  · rw [ENNReal.toReal_ne_zero]
    simp [hμ, measure_ne_top μ]
  · rw [ENNReal.toReal_ne_zero]
    simp [hν, measure_ne_top ν]

lemma kl_nonneg (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ kl μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · rw [kl_of_not_ac hμν]; simp
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · rw [kl_of_not_integrable h_int]; simp
  calc 0
    = ((μ Set.univ).toReal : EReal) * log ((μ Set.univ).toReal / (ν Set.univ).toReal) := by simp
  _ ≤ kl μ ν := kl_ge_mul_log μ ν

end kl_nonneg

section Conditional

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : kernel α β} {μ : Measure α}

open Classical in

-- TODO: choose the right definition between the following two
noncomputable
def condKL (κ η : kernel α β) (μ : Measure α) : EReal :=
  if (∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤)
    ∧ (Integrable (fun x ↦ (kl (κ x) (η x)).toReal) μ)
  then ((μ[fun x ↦ (kl (κ x) (η x)).toReal] : ℝ) : EReal)
  else ⊤

noncomputable
def condKL' (κ η : kernel α β) (μ : Measure α) : EReal :=
  condFDiv (fun x ↦ x * log x) κ η μ

lemma condKL_of_ae_finite_of_integrable (h1 : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤)
    (h2 : Integrable (fun x ↦ (kl (κ x) (η x)).toReal) μ) :
    condKL κ η μ = (μ[fun x ↦ (kl (κ x) (η x)).toReal] : ℝ) := if_pos ⟨h1, h2⟩

@[simp]
lemma condKL_of_not_ae_finite (h : ¬ (∀ᵐ x ∂μ, kl (κ x) (η x) ≠ ⊤)) :
    condKL κ η μ = ⊤ := if_neg (not_and_of_not_left _ h)

@[simp]
lemma condKL_of_not_ae_ac (h : ¬ (∀ᵐ x ∂μ, (κ x) ≪ (η x))) :
    condKL κ η μ = ⊤ := by
  apply condKL_of_not_ae_finite
  contrapose! h
  filter_upwards [h] with x hx
  contrapose! hx
  simp only [hx, not_false_eq_true, kl_of_not_ac]

@[simp]
lemma condKL_of_not_integrable (h : ¬ Integrable (fun x ↦ (kl (κ x) (η x)).toReal) μ) :
    condKL κ η μ = ⊤ := if_neg (not_and_of_not_right _ h)

--there seems not to be a property of kernels that says that ∀a κ a is sigma finite, but it seems to be exactly the one we would need in the following lemma, alternatively we could see if the lemma kl_eq_fDiv can be proved relaxing the hypothesis of sigma finiteness to SFinite

-- attempt to see if the hypothesys of sigma finiteness can be relaxed in
#check ProbabilityTheory.kl_eq_fDiv
--the hypothesis is needed by
#check ProbabilityTheory.fDiv_of_not_ac
-- which needs it for
#check MeasureTheory.Measure.singularPart_eq_zero
--which needs it for the instance that the two measures have a Lebesgue decomposition, in the case of sigma finite measures the instace is
#check MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite
--this seems to be an important theorem, so it may not be possible to generalize it, I found this paper (https://www.jstor.org/stable/2035430?seq=1) that seems to generalize it, but the result is a bit different than classical Lebesgue decomposition, so it may not be useful, maybe it's time to exit the rabbit hole
--I found another paper that seems to give the relevant result, this seems to be the classical decomposition but for s finite kernels, so it may be useful https://arxiv.org/pdf/1810.01837.pdf, still I don't know how much time it could take to formalize it

lemma condKL_eq_condFDiv [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    condKL κ η μ = condFDiv (fun x ↦ x * log x) κ η μ := by
  have : ∀ x, SigmaFinite (κ x) := by sorry --this should be substituted by some hypothesys, probabiliy the fact that the kernels are sigma finite
  have : ∀ x, SigmaFinite (η x) := by sorry --this should be substituted by some hypothesys, probabiliy the fact that the kernels are sigma finite
  by_cases h1 : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤
  swap;
  · simp [h1]
    refine (condFDiv_of_not_ae_finite ?_).symm
    convert h1 using 4 with x
    rw [kl_eq_fDiv]
  by_cases h2 : Integrable (fun x ↦ (kl (κ x) (η x)).toReal) μ
  swap;
  · simp [h2]
    refine (condFDiv_of_not_integrable ?_).symm
    convert h2 using 4 with x
    rw [← kl_eq_fDiv]
  simp only [ne_eq, h1, h2, condKL_of_ae_finite_of_integrable, ← kl_eq_fDiv, condFDiv_eq']

--TODO : add the corresponding lemma for the conditional f-divergence, then prove this one using that one, some hypothesis regarding sigma finiteness of the kernels will be needed
-- @[simp]
lemma condKL_self (κ : kernel α β) (μ : Measure α) : condKL κ κ μ = 0 := by
  -- rw [condKL_eq_condFDiv, condFDiv_self (by norm_num)]
  sorry

lemma condKL_ne_bot (κ η : kernel α β) (μ : Measure α) : condKL κ η μ ≠ ⊥ := by
  rw [condKL]
  split_ifs with h
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
  · norm_num
  
lemma condKL_nonneg (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] (μ : Measure α) :
    0 ≤ condKL κ η μ := by
  rw [condKL_eq_condFDiv]
  apply condFDiv_nonneg
  · exact Real.convexOn_mul_log
  · exact Real.continuous_mul_log.continuousOn
  · norm_num

--regarding the next 2 lemmas, should we keep them as they are (derived from the fDiv), or should we prove them using the kl_compProd? it's probabily better to leave them like this, since kl_compProd has slightly stronger hypothesis. Though maybe we can relax some of these hypothesis.
lemma kl_compProd_left [MeasurableSpace.CountablyGenerated β] (μ : Measure α) [IsFiniteMeasure μ] (κ η : kernel α β) [IsMarkovKernel κ] [IsFiniteKernel η] :
    kl (μ ⊗ₘ κ) (μ ⊗ₘ η) = condKL κ η μ := by
  rw [kl_eq_fDiv, condKL_eq_condFDiv]
  exact fDiv_compProd_left μ κ η (by measurability) Real.convexOn_mul_log

lemma kl_compProd_right [MeasurableSpace.CountablyGenerated β] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (κ : kernel α β) [IsMarkovKernel κ] :
    kl (μ ⊗ₘ κ) (ν ⊗ₘ κ) = kl μ ν := by
  rw [kl_eq_fDiv, kl_eq_fDiv]
  exact fDiv_compProd_right μ ν κ (by measurability) Real.convexOn_mul_log

-- TODO: build an API for the conditional KL divergence, see the one for the conditional f-divergence and the one for the KL divergence

#check ProbabilityTheory.kernel.rnDeriv_measure_compProd -- Lemma A.6
#check kernel.rnDeriv_eq_rnDeriv_measure -- Corollary A.2
#check ProbabilityTheory.kernel.Measure.absolutelyContinuous_compProd_iff

-- TODO: we are doing all the theory using natural log and eponential, is there any point in refactoring all to include the general case with arbitrary base?

#check kernel.Measure.absolutelyContinuous_compProd_iff.mpr.mt

lemma kl_compProd [StandardBorelSpace β] (κ η : kernel α β) [IsMarkovKernel κ] [IsFiniteKernel η] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl (μ ⊗ₘ κ) (ν ⊗ₘ η) = kl μ ν + condKL κ η μ := by
  by_cases comp_ac : (μ ⊗ₘ κ) ≪ (ν ⊗ₘ η)
  swap;
  · simp [comp_ac]
    have h := kernel.Measure.absolutelyContinuous_compProd_iff.mpr.mt comp_ac
    set_option push_neg.use_distrib true in push_neg at h
    rcases h with (hμν | hκη)
    · simp only [hμν, not_false_eq_true, kl_of_not_ac]
      -- refine (top_add_of_nonneg ?_).symm
      sorry
    · sorry
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · sorry -- address the case where the log likelihood ratio is not integrable
  have ⟨hμν, hκη⟩ := kernel.Measure.absolutelyContinuous_compProd_iff.mp comp_ac
  calc kl (μ ⊗ₘ κ) (ν ⊗ₘ η) = ↑(∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂(μ ⊗ₘ κ))  := by sorry
  _ = ↑(∫ (x : α), ∫ (y : β), llr (μ ⊗ₘ κ) (ν ⊗ₘ η) (x, y) ∂κ x ∂μ) := by
    norm_cast
    --refine Measure.integral_compProd ?_ --problem:here it seems that we need another assumption about finiteness of the measures and kernels
    sorry
  _ = ↑(∫ (x : α), ∫ (y : β), log ((∂μ/∂ν) x * kernel.rnDeriv κ η x y).toReal ∂κ x ∂μ) := by
    norm_cast
    have h := hμν.ae_le (Measure.ae_ae_of_ae_compProd (kernel.rnDeriv_measure_compProd μ ν κ η))
    apply integral_congr_ae
    filter_upwards [h, hκη] with x hx hκηx
    apply integral_congr_ae
    filter_upwards [hκηx.ae_le hx] with y hy
    unfold llr
    congr
  _ = ↑(∫ (x : α), ∫ (y : β), log (μ.rnDeriv ν x).toReal
      + log (kernel.rnDeriv κ η x y).toReal ∂κ x ∂μ) := by
    rcongr -- this is proably not the right tactic, because to say that the log of a product is the sum of the logs, we need to use the fact that the product is positive, but this is true only a.e., we need a lemma that says that the rnDeriv is positive a.e. wrt the relevant measures
    simp only [ENNReal.toReal_mul]
    apply log_mul
    sorry
    sorry
  _ = ↑(∫ (x : α), ∫ (y : β), log (μ.rnDeriv ν x).toReal ∂κ x ∂μ)
      + ↑(∫ (x : α), ∫ (y : β), log (kernel.rnDeriv κ η x y).toReal ∂κ x ∂μ) := by sorry
  _ = ↑(∫ (x : α), log (μ.rnDeriv ν x).toReal ∂μ)
      + ↑(∫ (x : α), ∫ (y : β), log (kernel.rnDeriv κ η x y).toReal ∂κ x ∂μ) := by
    simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  _ = ↑(∫ (x : α), log (μ.rnDeriv ν x).toReal ∂μ)
      + ↑(∫ (x : α), ∫ (y : β), log ((κ x).rnDeriv (η x) y).toReal ∂κ x ∂μ) := by
    congr 2
    apply integral_congr_ae
    filter_upwards [hκη] with x hx
    have h := hx.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η x)
    apply integral_congr_ae
    filter_upwards [h] with y hy
    congr
  _ = kl μ ν + condKL κ η μ := by
    congr
    · rw [← llr_def, ← kl_of_ac_of_integrable hμν h_int]
    · -- rw [condKL_of_ae_finite_of_integrable]
      -- rw [← llr_def, ← kl_of_ac_of_integrable hμν h_int]
      sorry


end Conditional

end ProbabilityTheory

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.FDiv.CondFDiv
import TestingLowerBounds.ForMathlib.IntegralCongr2
import TestingLowerBounds.ForMathlib.LogLikelihoodRatioCompProd

/-!
# Kullback-Leibler divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology BigOperators

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

/-- If `μ ≪ ν`, then `toReal` of the Kullback-Leibler divergence is equal to an integral,
without any integrability condition. Not true in general without `μ ≪ ν`, as the integral might be
finite but non-zero. -/
lemma kl_toReal_of_ac (h : μ ≪ ν) : (kl μ ν).toReal = ∫ a, llr μ ν a ∂μ := by
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [kl_of_ac_of_integrable h h_int, EReal.toReal_coe]
  · rw [kl_of_not_integrable h_int, integral_undef h_int, EReal.toReal_top]

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

@[simp]
lemma kl_zero_left : kl 0 ν = 0 := by
  convert kl_of_ac_of_integrable (Measure.AbsolutelyContinuous.zero _) integrable_zero_measure
  simp only [integral_zero_measure, EReal.coe_zero]

@[simp]
lemma kl_zero_right [NeZero μ] : kl μ 0 = ⊤ :=
  kl_of_not_ac (Measure.absolutelyContinuous_zero_iff.mp.mt (NeZero.ne _))

lemma kl_eq_top_iff : kl μ ν = ⊤ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ := by
  constructor <;> intro h <;> push_neg at *
  · contrapose! h
    rw [kl_of_ac_of_integrable h.1 h.2]
    exact EReal.coe_ne_top _
  · rcases or_not_of_imp h with (h | h) <;> simp [h]

lemma kl_ne_top_iff : kl μ ν ≠ ⊤ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ := by
  rw [ne_eq, kl_eq_top_iff]
  push_neg
  rfl

lemma kl_ne_top_iff' : kl μ ν ≠ ⊤ ↔ kl μ ν = ∫ x, llr μ ν x ∂μ := by
  constructor
  · rw [kl_ne_top_iff]
    rintro ⟨h1, h2⟩
    rw [kl_of_ac_of_integrable h1 h2]
  · simp_all only [ne_eq, EReal.coe_ne_top, not_false_eq_true, implies_true]

lemma measurable_kl {β : Type*} [MeasurableSpace β] [CountableOrCountablyGenerated α β]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦ kl (κ a) (η a)) := by
  simp_rw [kl_eq_fDiv]
  exact measurable_fDiv _ _ continuous_mul_log.stronglyMeasurable

section kl_nonneg

@[simp]
lemma kl_ne_bot (μ ν : Measure α) : kl μ ν ≠ ⊥ := by
  rw [kl]
  split_ifs with h
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
  · norm_num

lemma kl_ge_mul_log' [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (μ Set.univ).toReal * log (μ Set.univ).toReal ≤ kl μ ν :=
  (le_fDiv_of_ac convexOn_mul_log continuous_mul_log.continuousOn hμν).trans_eq
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
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  let ν' := (ν Set.univ)⁻¹ • ν
  have : IsProbabilityMeasure ν' := by
    constructor
    simp only [ν', Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
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

lemma kl_nonneg' (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ Set.univ ≥ ν Set.univ) :
    0 ≤ kl μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · rw [kl_of_not_ac hμν]; simp
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · rw [kl_of_not_integrable h_int]; simp
  calc 0
    ≤ ((μ Set.univ).toReal : EReal) * log ((μ Set.univ).toReal / (ν Set.univ).toReal) := by
        by_cases h_zero : NeZero ν
        swap; · simp [not_neZero.mp h_zero]
        refine mul_nonneg (EReal.coe_nonneg.mpr ENNReal.toReal_nonneg) ?_
        norm_cast
        refine log_nonneg ((one_le_div ?_).mpr ?_)
        · exact ENNReal.toReal_pos (NeZero.ne' _).symm (measure_ne_top _ _)
        · gcongr
          exact measure_ne_top _ _
  _ ≤ kl μ ν := kl_ge_mul_log _ _

/-- **Gibbs' inequality**: the Kullback-Leibler divergence between two probability distributions is
nonnegative. -/
lemma kl_nonneg (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ kl μ ν := kl_nonneg' μ ν (by simp)

/-- **Converse Gibbs' inequality**: the Kullback-Leibler divergence between two finite measures is
zero if and only if the two distributions are equal. -/
lemma kl_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_mass : μ Set.univ = ν Set.univ) :
    kl μ ν = 0 ↔ μ = ν :=
  kl_eq_fDiv (μ := μ) (ν := ν) ▸ fDiv_eq_zero_iff h_mass derivAtTop_mul_log
    Real.strictConvexOn_mul_log Real.continuous_mul_log.continuousOn (by norm_num)

/-- **Converse Gibbs' inequality**: the Kullback-Leibler divergence between two probability
distributions is zero if and only if the two distributions are equal. -/
lemma kl_eq_zero_iff' [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    kl μ ν = 0 ↔ μ = ν := kl_eq_zero_iff (by simp)

end kl_nonneg

section Conditional

variable {β γ : Type*} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {κ η : kernel α β}

/--Equivalence between two possible versions of the first condition for the finiteness of the
conditional KL divergence, the second version is the preferred one.-/
lemma kl_ae_ne_top_iff : (∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤) ↔
    (∀ᵐ a ∂μ, κ a ≪ η a) ∧ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) := by
  simp_rw [kl_ne_top_iff, eventually_and]

/--Equivalence between two possible versions of the second condition for the finiteness of the
conditional KL divergence, the first version is the preferred one.-/
lemma integrable_kl_iff (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ
      ↔ Integrable (fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)) μ := by
  apply integrable_congr
  filter_upwards [h_ac] with a ha1
  rw [kl_toReal_of_ac ha1]

open Classical in

/--
Kullback-Leibler divergence between two kernels κ and η conditional to a measure μ.
It is defined as KL(κ, η | μ) := ∫ x, KL(κ x, η x) dμ.
-/
noncomputable
def condKL (κ η : kernel α β) (μ : Measure α) : EReal :=
  if (∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤)
    ∧ (Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ)
  then ((μ[fun a ↦ (kl (κ a) (η a)).toReal] : ℝ) : EReal)
  else ⊤

section CondKLEq

lemma condKL_of_ae_ne_top_of_integrable (h1 : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤)
    (h2 : Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = (μ[fun a ↦ (kl (κ a) (η a)).toReal] : ℝ) := if_pos ⟨h1, h2⟩

lemma condKL_of_ae_ac_of_ae_integrable_of_integrable (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a)
    (h_ae_int : ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
    (h_int : Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = (μ[fun a ↦ (kl (κ a) (η a)).toReal] : ℝ) :=
  condKL_of_ae_ne_top_of_integrable (kl_ae_ne_top_iff.mpr ⟨h_ac, h_ae_int⟩) h_int

lemma condKL_of_ae_ac_of_ae_integrable_of_integrable' (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a)
    (h_ae_int : ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
    (h_int : Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = (μ[fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)] : ℝ) := by
  rw [condKL_of_ae_ac_of_ae_integrable_of_integrable h_ac h_ae_int h_int]
  congr 1
  apply integral_congr_ae
  filter_upwards [h_ac] with a ha1
  rw [kl_toReal_of_ac ha1]

@[simp]
lemma condKL_of_not_ae_ne_top (h : ¬ (∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤)) :
    condKL κ η μ = ⊤ := if_neg (not_and_of_not_left _ h)

@[simp]
lemma condKL_of_not_ae_ac (h : ¬ ∀ᵐ a ∂μ, κ a ≪ η a) :
    condKL κ η μ = ⊤ := by
  apply condKL_of_not_ae_ne_top
  rw [kl_ae_ne_top_iff]
  tauto

@[simp]
lemma condKL_of_not_ae_integrable (h : ¬ ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) :
    condKL κ η μ = ⊤ := by
  apply condKL_of_not_ae_ne_top
  rw [kl_ae_ne_top_iff]
  tauto

@[simp]
lemma condKL_of_not_integrable (h : ¬ Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = ⊤ := if_neg (not_and_of_not_right _ h)

@[simp]
lemma condKL_of_not_integrable' (h : ¬ Integrable (fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)) μ) :
    condKL κ η μ = ⊤ := by
  by_cases h_ne_top : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤
  swap; exact condKL_of_not_ae_ne_top h_ne_top
  apply condKL_of_not_integrable
  rwa [integrable_kl_iff (kl_ae_ne_top_iff.mp h_ne_top).1]

lemma condKL_toReal_of_ae_ac_of_ae_integrable (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a)
    (h_ae_int : ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) :
    (condKL κ η μ).toReal = μ[fun a ↦ (kl (κ a) (η a)).toReal] := by
  by_cases h_int : Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ
  · rw [condKL_of_ae_ac_of_ae_integrable_of_integrable h_ac h_ae_int h_int, EReal.toReal_coe]
  · rw [condKL_of_not_integrable h_int, integral_undef h_int, EReal.toReal_top]

lemma condKL_eq_top_iff : condKL κ η μ = ⊤ ↔
    ¬ (∀ᵐ a ∂μ, κ a ≪ η a) ∨ ¬ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
    ∨ ¬ Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ := by
  constructor <;> intro h
  · contrapose! h
    rw [condKL_of_ae_ac_of_ae_integrable_of_integrable h.1 h.2.1 h.2.2]
    exact EReal.coe_ne_top _
  · rcases h with (h | h | h) <;>
      simp only [h, not_false_eq_true, condKL_of_not_ae_ac, condKL_of_not_ae_integrable,
        condKL_of_not_integrable]

lemma condKL_ne_top_iff : condKL κ η μ ≠ ⊤ ↔
    (∀ᵐ a ∂μ, κ a ≪ η a) ∧ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
    ∧ Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ := by
  rw [ne_eq, condKL_eq_top_iff]
  push_neg
  rfl

lemma condKL_ne_top_iff' : condKL κ η μ ≠ ⊤
    ↔ condKL κ η μ = (μ[fun a ↦ (kl (κ a) (η a)).toReal] : ℝ) := by
  constructor
  · rw [condKL_ne_top_iff]
    exact fun ⟨h1, h2, h3⟩ ↦ condKL_of_ae_ac_of_ae_integrable_of_integrable h1 h2 h3
  · simp_all only [ne_eq, EReal.coe_ne_top, not_false_eq_true, implies_true]

end CondKLEq

lemma condKL_eq_condFDiv [IsFiniteKernel κ] [IsFiniteKernel η] :
    condKL κ η μ = condFDiv (fun x ↦ x * log x) κ η μ := by
  by_cases h1 : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤
  swap
  · simp only [ne_eq, h1, not_false_eq_true, condKL_of_not_ae_ne_top]
    refine (condFDiv_of_not_ae_finite ?_).symm
    convert h1 using 4 with a
    rw [kl_eq_fDiv]
  by_cases h2 : Integrable (fun x ↦ (kl (κ x) (η x)).toReal) μ
  swap
  · simp only [h2, not_false_eq_true, condKL_of_not_integrable]
    refine (condFDiv_of_not_integrable ?_).symm
    convert h2 using 4 with a
    rw [← kl_eq_fDiv]
  simp only [ne_eq, h1, h2, condKL_of_ae_ne_top_of_integrable, ← kl_eq_fDiv, condFDiv_eq']

@[simp]
lemma condKL_self (κ : kernel α β) (μ : Measure α) [IsFiniteKernel κ] : condKL κ κ μ = 0 := by
  simp only [kl_self, ne_eq, not_false_eq_true, eventually_true, EReal.toReal_zero, integrable_zero,
    condKL_of_ae_ne_top_of_integrable, integral_zero, EReal.coe_zero, EReal.zero_ne_top]

@[simp]
lemma condKL_zero_left : condKL 0 η μ = 0 := by
  rw [condKL_of_ae_ne_top_of_integrable _ _]
  · simp only [kernel.zero_apply, kl_zero_left, EReal.toReal_zero, integral_zero, EReal.coe_zero]
  · simp only [kernel.zero_apply, kl_zero_left, ne_eq, EReal.zero_ne_top, not_false_eq_true,
      eventually_true]
  · simp only [kernel.zero_apply, kl_zero_left, EReal.toReal_zero, integrable_zero]

@[simp]
lemma condKL_zero_right (h : ∃ᵐ a ∂μ, κ a ≠ 0) : condKL κ 0 μ = ⊤ := by
  simp only [kernel.zero_apply, Measure.absolutelyContinuous_zero_iff, not_eventually, h,
    condKL_of_not_ae_ac]

@[simp]
lemma condKL_zero_measure : condKL κ η 0 = 0 := by
  have hf_ae : ∀ᵐ a ∂(0 : Measure α), kl (κ a) (η a) ≠ ⊤ := by
    simp only [ne_eq, ae_zero, eventually_bot]
  rw [condKL_of_ae_ne_top_of_integrable hf_ae integrable_zero_measure]
  simp only [integral_zero_measure, EReal.coe_zero]

@[simp]
lemma condKL_isEmpty_left [IsEmpty α] : condKL κ η μ = 0 := by
  have h : μ = 0 := by
    ext s
    exact Set.eq_empty_of_isEmpty s ▸ measure_empty
  exact h ▸ condKL_zero_measure

lemma condKL_ne_bot (κ η : kernel α β) (μ : Measure α) : condKL κ η μ ≠ ⊥ := by
  rw [condKL]
  split_ifs with h
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
  · norm_num

lemma condKL_nonneg (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] (μ : Measure α) :
    0 ≤ condKL κ η μ := by
  rw [condKL_eq_condFDiv]
  exact condFDiv_nonneg convexOn_mul_log continuous_mul_log.continuousOn (by norm_num)

@[simp]
lemma condKL_const {ξ : Measure β} [IsFiniteMeasure ξ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    condKL (kernel.const β μ) (kernel.const β ν) ξ = (kl μ ν) * ξ Set.univ := by
  rw [condKL_eq_condFDiv, kl_eq_fDiv]
  exact condFDiv_const

lemma kl_fst_le [Nonempty β] [StandardBorelSpace β]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ.fst ν.fst ≤ kl μ ν := by
  simp_rw [kl_eq_fDiv]
  exact fDiv_fst_le _ _ continuous_mul_log.stronglyMeasurable convexOn_mul_log
    continuous_mul_log.continuousOn

lemma kl_snd_le [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ.snd ν.snd ≤ kl μ ν := by
  simp_rw [kl_eq_fDiv]
  exact fDiv_snd_le _ _ continuous_mul_log.stronglyMeasurable convexOn_mul_log
    continuous_mul_log.continuousOn

section CompProd

lemma le_kl_compProd [CountableOrCountablyGenerated α β] (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    kl μ ν ≤ kl (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simp_rw [kl_eq_fDiv]
  exact le_fDiv_compProd μ ν κ η continuous_mul_log.stronglyMeasurable
    convexOn_mul_log continuous_mul_log.continuousOn

/- TODO: the following lemma may be generalized, infact the hypothesys of being markov kernels is
only used to prove that
`Integrable (fun x ↦ ∫ (y : β), ‖EReal.toReal (kl (κ (x, y)) (η (x, y)))‖ ∂ξ x) μ` is true,
given that `Integrable (fun x ↦ ∫ (y : β), EReal.toReal (kl (κ (x, y)) (η (x, y))) ∂ξ x` but if
the kernels are finite then the kl is bounded from below, so it should be still possible to conclude
the integrability of the first function, this would however require more work. -/
/-- This is to handle the case in `condKL_compProd_meas` when the lhs is ⊤, in this case the rhs is
'morally' also ⊤, so the equality holds, but actually in Lean the equality is not true, because of
how we handle the infinities in the integrals, so we have to make a separate lemma for this case. -/
lemma condKL_compProd_meas_eq_top [CountableOrCountablyGenerated (α × β) γ] [SFinite μ]
    {ξ : kernel α β} [IsSFiniteKernel ξ] {κ η : kernel (α × β) γ}
    [IsMarkovKernel κ] [IsMarkovKernel η] :
    condKL κ η (μ ⊗ₘ ξ) = ⊤
      ↔ ¬ (∀ᵐ a ∂μ, condKL (kernel.snd' κ a) (kernel.snd' η a) (ξ a) ≠ ⊤)
        ∨ ¬ Integrable (fun x ↦ (condKL (kernel.snd' κ x) (kernel.snd' η x) (ξ x)).toReal) μ := by
  rw [condKL_eq_top_iff]
  have h_ae_eq (h_ae : ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, κ (a, b) ≪ η (a, b))
      (h_int : ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, Integrable (llr (κ (a, b)) (η (a, b))) (κ (a, b))) :
      (fun x ↦ (condKL (kernel.snd' κ x) (kernel.snd' η x) (ξ x)).toReal)
        =ᵐ[μ] fun a ↦ ∫ b, (kl (κ (a, b)) (η (a, b))).toReal ∂ξ a := by
    filter_upwards [h_ae, h_int] with a ha_ae ha_int
    rw [condKL_toReal_of_ae_ac_of_ae_integrable]
    · simp only [kernel.snd'_apply]
    · filter_upwards [ha_ae] with b hb using kernel.snd'_apply _ _ _ ▸ hb
    · filter_upwards [ha_int] with b hb using kernel.snd'_apply _ _ _ ▸ hb
  constructor
  · by_cases h_ae : ∀ᵐ x ∂(μ ⊗ₘ ξ), κ x ≪ η x
    swap
    · rw [Measure.ae_compProd_iff (kernel.measurableSet_absolutelyContinuous _ _)] at h_ae
      simp_rw [condKL_ne_top_iff, kernel.snd'_apply, eventually_and, not_and_or]
      intro; left; left
      exact h_ae
    by_cases h_int : ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, Integrable (llr (κ (a, b)) (η (a, b))) (κ (a, b))
    swap
    · simp only [condKL_ne_top_iff, not_eventually, kernel.snd'_apply, eventually_and, h_int,
        false_and, and_false, not_false_eq_true, true_or, implies_true]
    simp only [not_true_eq_false, false_or, ne_eq, not_eventually, not_not, h_ae,
      (ae_compProd_integrable_llr_iff h_ae).mpr h_int]
    rw [Measure.integrable_compProd_iff
      (measurable_kl κ η).ereal_toReal.stronglyMeasurable.aestronglyMeasurable]
    push_neg
    intro h
    by_cases h_int2 : ∀ᵐ a ∂μ, Integrable (fun b ↦ (kl (κ (a, b)) (η (a, b))).toReal) (ξ a)
    swap
    · left
      contrapose! h_int2
      rw [not_frequently] at h_int2
      filter_upwards [h_int2] with a ha_int2
      simp only [condKL_ne_top_iff, kernel.snd'_apply] at ha_int2
      exact ha_int2.2.2
    right
    rw [Measure.ae_compProd_iff (kernel.measurableSet_absolutelyContinuous _ _)] at h_ae
    apply Integrable.congr.mt
    swap; exact fun a ↦ ∫ b, (kl (κ (a, b)) (η (a, b))).toReal ∂(ξ a)
    push_neg
    constructor
    · exact h_ae_eq h_ae h_int
    · replace h := h h_int2
      contrapose! h
      convert h with a b
      simp only [norm_eq_abs, abs_eq_self]
      exact EReal.toReal_nonneg (kl_nonneg _ _)
  · intro h
    contrapose! h
    obtain ⟨h_ae, ⟨h_int1, h_int2⟩⟩ := h
    rw [ae_compProd_integrable_llr_iff h_ae] at h_int1
    rw [Measure.ae_compProd_iff (kernel.measurableSet_absolutelyContinuous _ _)] at h_ae
    have h_meas := (Integrable.integral_compProd' h_int2).aestronglyMeasurable
    rw [Measure.integrable_compProd_iff h_int2.aestronglyMeasurable] at h_int2
    constructor
    · filter_upwards [h_ae, h_int1, h_int2.1] with a ha_ae ha_int ha_int2
      apply condKL_ne_top_iff.mpr
      simp only [kernel.snd'_apply]
      exact ⟨ha_ae, ⟨ha_int, ha_int2⟩⟩
    · refine Integrable.congr ?_ (h_ae_eq h_ae h_int1).symm
      replace h_int := h_int2.2
      apply Integrable.mono h_int h_meas
      refine ae_of_all μ fun a ↦ ?_
      calc ‖∫ b, (kl (κ (a, b)) (η (a, b))).toReal ∂ξ a‖
      _ ≤ ∫ b, ‖(kl (κ (a, b)) (η (a, b))).toReal‖ ∂ξ a :=
        norm_integral_le_integral_norm _
      _ = _ := by
        simp only [norm_eq_abs]
        apply (abs_of_nonneg _).symm
        positivity

-- TODO: find a better name
lemma condKL_compProd_meas [CountableOrCountablyGenerated (α × β) γ] [SFinite μ] {ξ : kernel α β}
    [IsSFiniteKernel ξ] {κ η : kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h : condKL κ η (μ ⊗ₘ ξ) ≠ ⊤) :
    condKL κ η (μ ⊗ₘ ξ) = ∫ x, (condKL (kernel.snd' κ x) (kernel.snd' η x) (ξ x)).toReal ∂μ := by
  rw [condKL_ne_top_iff'.mp h, Measure.integral_compProd (condKL_ne_top_iff.mp h).2.2]
  replace h := condKL_compProd_meas_eq_top.mpr.mt h
  push_neg at h
  norm_cast
  apply integral_congr_ae
  filter_upwards [h.1] with a ha
  simp_rw [condKL_ne_top_iff'.mp ha, EReal.toReal_coe, kernel.snd'_apply]

lemma kl_compProd_left [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [∀ x, NeZero (κ x)] [IsFiniteKernel η] :
    kl (μ ⊗ₘ κ) (μ ⊗ₘ η) = condKL κ η μ := by
  rw [kl_eq_fDiv, condKL_eq_condFDiv]
  exact fDiv_compProd_left μ κ η continuous_mul_log.stronglyMeasurable convexOn_mul_log

lemma kl_compProd_right (κ : kernel α β) [CountableOrCountablyGenerated α β] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [IsMarkovKernel κ] :
    kl (μ ⊗ₘ κ) (ν ⊗ₘ κ) = kl μ ν := by
  rw [kl_eq_fDiv, kl_eq_fDiv]
  exact fDiv_compProd_right μ ν κ continuous_mul_log.stronglyMeasurable convexOn_mul_log


/--The chain rule for the KL divergence.-/
lemma kl_compProd [CountableOrCountablyGenerated α β] [IsMarkovKernel κ] [IsMarkovKernel η]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl (μ ⊗ₘ κ) (ν ⊗ₘ η) = kl μ ν + condKL κ η μ := by
  by_cases h_prod : (μ ⊗ₘ κ) ≪ (ν ⊗ₘ η)
  swap
  · simp only [h_prod, not_false_eq_true, kl_of_not_ac]
    have h := kernel.Measure.absolutelyContinuous_compProd_iff.mpr.mt h_prod
    set_option push_neg.use_distrib true in push_neg at h
    rcases h with (hμν | hκη)
    · simp only [hμν, not_false_eq_true, kl_of_not_ac]
      exact (EReal.top_add_of_ne_bot (condKL_ne_bot _ _ _)).symm
    · simp only [hκη, not_false_eq_true, condKL_of_not_ae_ac]
      exact (EReal.add_top_of_ne_bot (kl_ne_bot _ _)).symm
  have ⟨hμν, hκη⟩ := kernel.Measure.absolutelyContinuous_compProd_iff.mp h_prod
  by_cases h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)
  swap
  · simp only [h_int, not_false_eq_true, kl_of_not_integrable]
    rw [integrable_llr_compProd_iff h_prod] at h_int
    set_option push_neg.use_distrib true in push_neg at h_int
    rcases h_int with ((h | h) | h) <;>
      simp only [h, not_false_eq_true, kl_of_not_integrable, ne_eq, EReal.top_add_of_ne_bot,
        condKL_ne_bot, condKL_of_not_integrable', EReal.add_top_of_ne_bot, kl_ne_bot,
        condKL_of_not_ae_integrable]
  have intμν := integrable_llr_of_integrable_llr_compProd h_prod h_int
  have intκη : Integrable (fun a ↦ ∫ (x : β), log (kernel.rnDeriv κ η a x).toReal ∂κ a) μ := by
    apply Integrable.congr (integrable_integral_llr_of_integrable_llr_compProd h_prod h_int)
    filter_upwards [hκη] with a ha
    apply integral_congr_ae
    filter_upwards [ha.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η a)] with x hx
    rw [hx, llr_def]
  have intκη2 := ae_integrable_llr_of_integrable_llr_compProd h_prod h_int
  calc kl (μ ⊗ₘ κ) (ν ⊗ₘ η) = ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂(μ ⊗ₘ κ) :=
    kl_of_ac_of_integrable h_prod h_int
  _ = ∫ a, ∫ x, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) (a, x) ∂κ a ∂μ := mod_cast Measure.integral_compProd h_int
  _ = ∫ a, ∫ x, log (μ.rnDeriv ν a).toReal
      + log (kernel.rnDeriv κ η a x).toReal ∂κ a ∂μ := by
    norm_cast
    have h := hμν.ae_le (Measure.ae_ae_of_ae_compProd (kernel.rnDeriv_measure_compProd μ ν κ η))
    apply integral_congr_ae₂
    filter_upwards [h, hκη, Measure.rnDeriv_toReal_pos hμν] with a ha hκηa hμν_pos
    have hμν_zero : (μ.rnDeriv ν a).toReal ≠ 0 := by linarith
    filter_upwards [kernel.rnDeriv_toReal_pos hκηa, hκηa.ae_le ha] with x hκη_pos hx
    have hκη_zero : (kernel.rnDeriv κ η a x).toReal ≠ 0 := by linarith
    rw [llr, hx, ENNReal.toReal_mul]
    exact log_mul hμν_zero hκη_zero
  _ = ∫ a, ∫ _, log (μ.rnDeriv ν a).toReal ∂κ a ∂μ
      + ∫ a, ∫ x, log (kernel.rnDeriv κ η a x).toReal ∂κ a ∂μ := by
    norm_cast
    rw [← integral_add']
    simp only [Pi.add_apply]
    rotate_left
    · simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul, ← llr_def]
      exact intμν
    · exact intκη
    apply integral_congr_ae
    filter_upwards [hκη, intκη2] with a ha hκηa
    have h := ha.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η a)
    rw [← integral_add']
    rotate_left
    · simp only [integrable_const]
    · apply Integrable.congr hκηa
      filter_upwards [h] with x hx
      rw [hx, llr_def]
    apply integral_congr_ae
    filter_upwards with a
    congr
  _ = ∫ a, log (μ.rnDeriv ν a).toReal ∂μ
      + ∫ a, ∫ x, log ((κ a).rnDeriv (η a) x).toReal ∂κ a ∂μ := by
    simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
    congr 2
    apply integral_congr_ae₂
    filter_upwards [hκη] with a ha
    have h := ha.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η a)
    filter_upwards [h] with x hx
    congr
  _ = kl μ ν + condKL κ η μ := by
    congr <;> simp_rw [← llr_def]
    · rw [← kl_of_ac_of_integrable hμν intμν]
    · rw [condKL_of_ae_ac_of_ae_integrable_of_integrable' hκη intκη2 _]
      apply (integrable_kl_iff hκη).mpr
      simp_rw [llr_def]
      apply Integrable.congr intκη
      filter_upwards [hκη] with a ha
      have h := ha.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η a)
      apply integral_congr_ae
      filter_upwards [h] with x hx
      rw [hx]

/--The chain rule for the KL divergence.-/
lemma kl_fst_add_condKL [StandardBorelSpace β] [Nonempty β] {μ ν : Measure (α × β)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ.fst ν.fst + condKL μ.condKernel ν.condKernel μ.fst = kl μ ν := by
  rw [← kl_compProd, μ.compProd_fst_condKernel, ν.compProd_fst_condKernel]

/-TODO: this is just a thin wrapper around kernel.integrable_llr_compProd_iff, so that that lemma
could be put in an outside file. But I have realised that the choice of having 2 instead of 2' as
the hp of choice about integrability here may be a bad one, because in cases like this one
it does not allow to move stuff outside this file, as it relies on the definition of kl.
Moreover in general it is the opposite choice to what is done in fDiv, and in fDiv the other choice
is much more convenient, because it allows to disregard the singular part inside the definition of
fDiv when talking about integrability. So I think it may be better to reverse this choice here,
changing the lemmas like condKL_ne_top_iff from 2 to 2'-/
lemma kernel.integrable_llr_compProd_iff' [CountableOrCountablyGenerated β γ]
    {κ₁ η₁ : kernel α β} {κ₂ η₂ : kernel (α × β) γ} [IsFiniteKernel κ₁] [IsFiniteKernel η₁]
    [IsMarkovKernel κ₂] [IsMarkovKernel η₂] (a : α) (h_ac : (κ₁ ⊗ₖ κ₂) a ≪ (η₁ ⊗ₖ η₂) a) :
    Integrable (llr ((κ₁ ⊗ₖ κ₂) a) ((η₁ ⊗ₖ η₂) a)) ((κ₁ ⊗ₖ κ₂) a)
      ↔ Integrable (llr (κ₁ a) (η₁ a)) (κ₁ a)
        ∧ Integrable (fun b ↦ (kl (κ₂ (a, b)) (η₂ (a, b))).toReal) (κ₁ a)
        ∧ ∀ᵐ b ∂κ₁ a, Integrable (llr (κ₂ (a, b)) (η₂ (a, b))) (κ₂ (a, b)) := by
  convert kernel.integrable_llr_compProd_iff a h_ac using 3
  simp_rw [← kernel.snd'_apply]
  have h_ac' := kernel.absolutelyContinuous_compProd_iff a |>.mp h_ac |>.2
  exact integrable_kl_iff h_ac'

lemma kl_compProd_kernel_of_ae_ac_of_ae_integrable [CountableOrCountablyGenerated β γ]
    {κ₁ η₁ : kernel α β} {κ₂ η₂ : kernel (α × β) γ} [IsFiniteKernel κ₁] [IsFiniteKernel η₁]
    [IsMarkovKernel κ₂] [IsMarkovKernel η₂] (h_ac : ∀ᵐ a ∂μ, (κ₁ ⊗ₖ κ₂) a ≪ (η₁ ⊗ₖ η₂) a)
    (h_ae_int : ∀ᵐ a ∂μ, Integrable (llr ((κ₁ ⊗ₖ κ₂) a) ((η₁ ⊗ₖ η₂) a)) ((κ₁ ⊗ₖ κ₂) a)) :
    ∀ᵐ a ∂μ, (kl ((κ₁ ⊗ₖ κ₂) a) ((η₁ ⊗ₖ η₂) a)).toReal
      = (kl (κ₁ a) (η₁ a)).toReal + ∫ b, (kl (κ₂ (a, b)) (η₂ (a, b))).toReal ∂κ₁ a := by
  simp only [eventually_congr (h_ac.mono (fun a h ↦ (kernel.integrable_llr_compProd_iff' a h))),
    eventually_and] at h_ae_int
  simp only [kernel.absolutelyContinuous_compProd_iff, eventually_and] at h_ac
  filter_upwards [h_ac.1, h_ac.2, h_ae_int.1, h_ae_int.2.1, h_ae_int.2.2] with a ha_ac₁ ha_ac₂
    ha_int₁ ha_int_kl₂ ha_int₂
  have h_snd_ne_top : condKL (kernel.snd' κ₂ a) (kernel.snd' η₂ a) (κ₁ a) ≠ ⊤ := by
    apply condKL_ne_top_iff.mpr
    simp_rw [kernel.snd'_apply]
    exact ⟨ha_ac₂, ⟨ha_int₂, ha_int_kl₂⟩⟩
  simp_rw [kernel.compProd_apply_eq_compProd_snd', kl_compProd,
    EReal.toReal_add (kl_ne_top_iff.mpr ⟨ha_ac₁, ha_int₁⟩) (kl_ne_bot (κ₁ a) (η₁ a)) h_snd_ne_top
    (condKL_ne_bot (kernel.snd' κ₂ a) (kernel.snd' η₂ a) (κ₁ a)),
    condKL_ne_top_iff'.mp h_snd_ne_top, EReal.toReal_coe, kernel.snd'_apply]

lemma condKL_compProd_kernel_eq_top [CountableOrCountablyGenerated (α × β) γ] {κ₁ η₁ : kernel α β}
    {κ₂ η₂ : kernel (α × β) γ} [IsMarkovKernel κ₁] [IsMarkovKernel η₁] [IsMarkovKernel κ₂]
    [IsMarkovKernel η₂] [SFinite μ] :
    condKL (κ₁ ⊗ₖ κ₂) (η₁ ⊗ₖ η₂) μ = ⊤ ↔ condKL κ₁ η₁ μ = ⊤ ∨ condKL κ₂ η₂ (μ ⊗ₘ κ₁) = ⊤ := by
  by_cases h_empty : Nonempty α
  swap
  · replace h_empty := not_nonempty_iff.mp h_empty
    simp only [condKL_isEmpty_left]
    tauto
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  simp_rw [condKL_eq_top_iff,
    Measure.ae_compProd_iff (kernel.measurableSet_absolutelyContinuous _ _)]
  by_cases h_ac : ∀ᵐ a ∂μ, (κ₁ ⊗ₖ κ₂) a ≪ (η₁ ⊗ₖ η₂) a
    <;> have h_ac' := h_ac
    <;> simp only [kernel.absolutelyContinuous_compProd_iff, eventually_and, not_and_or] at h_ac'
    <;> simp only [h_ac, h_ac', not_false_eq_true, true_or, not_true, true_iff, false_or]
  swap; tauto
  rw [← Measure.ae_compProd_iff (kernel.measurableSet_absolutelyContinuous _ _)] at h_ac'
  by_cases h_ae_int : ∀ᵐ a ∂μ, Integrable (llr ((κ₁ ⊗ₖ κ₂) a) ((η₁ ⊗ₖ η₂) a)) ((κ₁ ⊗ₖ κ₂) a)
    <;> have h_ae_int' := h_ae_int
    <;> simp only [eventually_congr (h_ac.mono (fun a h ↦ (kernel.integrable_llr_compProd_iff' a h))),
      eventually_and, not_and_or] at h_ae_int'
    <;> simp only [h_ae_int, h_ae_int', not_false_eq_true, true_or, true_and, not_true, true_iff,
      false_or, not_and_or, ae_compProd_integrable_llr_iff h_ac'.2, Measure.integrable_compProd_iff
      (measurable_kl _ _).ereal_toReal.stronglyMeasurable.aestronglyMeasurable]
  swap
  · by_cases h_int₁ : ∀ᵐ x ∂μ, Integrable (llr (κ₁ x) (η₁ x)) (κ₁ x)
    swap; tauto
    by_cases h_int₂ : ∀ᵐ a ∂μ, ∀ᵐ b ∂κ₁ a, Integrable (llr (κ₂ (a, b)) (η₂ (a, b))) (κ₂ (a, b))
    swap; tauto
    simp only [h_int₁, h_int₂, not_true_eq_false, false_or, or_false] at h_ae_int'
    right; right; left
    exact h_ae_int'
  simp only [norm_eq_abs, EReal.toReal_nonneg (kl_nonneg _ _), abs_of_nonneg, ← not_and_or,
    not_iff_not]
  rw [integrable_congr (kl_compProd_kernel_of_ae_ac_of_ae_integrable h_ac h_ae_int), and_comm]
  simp_rw [add_comm (kl (κ₁ _) (η₁ _)).toReal]
  apply integrable_add_iff_of_nonneg
  · exact StronglyMeasurable.integral_kernel_prod_right' (κ := κ₁)
      ((measurable_kl κ₂ η₂).ereal_toReal.stronglyMeasurable) |>.aestronglyMeasurable
  · filter_upwards with a using integral_nonneg (fun b ↦ EReal.toReal_nonneg (kl_nonneg _ _))
  · filter_upwards with a using EReal.toReal_nonneg (kl_nonneg _ _)

lemma condKL_compProd_kernel [CountableOrCountablyGenerated (α × β) γ] {κ₁ η₁ : kernel α β}
    {κ₂ η₂ : kernel (α × β) γ} [IsMarkovKernel κ₁] [IsMarkovKernel η₁] [IsMarkovKernel κ₂]
    [IsMarkovKernel η₂] [SFinite μ] :
    condKL (κ₁ ⊗ₖ κ₂) (η₁ ⊗ₖ η₂) μ = condKL κ₁ η₁ μ + condKL κ₂ η₂ (μ ⊗ₘ κ₁) := by
  by_cases h_empty : Nonempty α
  swap
  · replace h_empty := not_nonempty_iff.mp h_empty
    simp only [condKL_isEmpty_left, zero_add]
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  by_cases hp : condKL (κ₁ ⊗ₖ κ₂) (η₁ ⊗ₖ η₂) μ = ⊤
  · rw [hp]
    rw [condKL_compProd_kernel_eq_top] at hp
    rcases hp with (h | h) <;> rw [h]
    · exact (EReal.top_add_of_ne_bot (condKL_ne_bot _ _ _)).symm
    · exact (EReal.add_top_of_ne_bot (condKL_ne_bot _ _ _)).symm
  obtain ⟨h1, h2⟩ := not_or.mp <| condKL_compProd_kernel_eq_top.mpr.mt hp
  rw [condKL_ne_top_iff'.mp hp, condKL_ne_top_iff'.mp h1, condKL_ne_top_iff'.mp h2]
  rw [← ne_eq, condKL_ne_top_iff] at h1 h2 hp
  rw [Measure.integral_compProd h2.2.2]
  norm_cast
  convert integral_add h1.2.2 (Integrable.integral_compProd' h2.2.2) using 1
  exact integral_congr_ae <| kl_compProd_kernel_of_ae_ac_of_ae_integrable hp.1 hp.2.1

end CompProd

end Conditional

section Tensorization

variable {β : Type*} {mβ : MeasurableSpace β}

lemma kl_prod_two' [CountableOrCountablyGenerated α β] {ξ ψ : Measure β} [IsProbabilityMeasure ξ]
    [IsProbabilityMeasure ψ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]:
    kl (μ.prod ξ) (ν.prod ψ) = kl μ ν + kl ξ ψ * (μ Set.univ) := by
  simp only [← condKL_const, ← kl_compProd, Measure.compProd_const]

/--Tensorization property for KL divergence-/
lemma kl_prod_two [CountableOrCountablyGenerated α β] {ξ ψ : Measure β} [IsProbabilityMeasure ξ]
    [IsProbabilityMeasure ψ] [IsProbabilityMeasure μ] [IsFiniteMeasure ν] :
    kl (μ.prod ξ) (ν.prod ψ) = kl μ ν + kl ξ ψ := by
  simp only [kl_prod_two', measure_univ, EReal.coe_ennreal_one, mul_one]

--TODO: put this in the right place, maybe PR to mathlib, just after MeasurableEquiv.piCongrLeft?
-- The following 3 lemmas have been PRed, see #13311
lemma MeasurableEquiv.piCongrLeft_apply_apply {ι ι' : Type*} (e : ι ≃ ι') {β : ι' → Type*}
    [∀ i', MeasurableSpace (β i')] (x : (i : ι) → β (e i)) (i : ι) :
    (MeasurableEquiv.piCongrLeft (fun i' ↦ β i') e) x (e i) = x i := by
  rw [MeasurableEquiv.piCongrLeft, MeasurableEquiv.coe_mk, Equiv.piCongrLeft_apply_apply]

lemma Measure.pi_map_piCongrLeft {ι ι' : Type*} [hι : Fintype ι] [hι' : Fintype ι'] (e : ι ≃ ι')
    {β : ι' → Type*} [∀ i, MeasurableSpace (β i)] (μ : (i : ι') → Measure (β i))
    [∀ i, SigmaFinite (μ i)] :
    (Measure.pi fun i ↦ μ (e i)).map (MeasurableEquiv.piCongrLeft (fun i ↦ β i) e)
    = Measure.pi μ := by
  let e_meas : ((b : ι) → β (e b)) ≃ᵐ ((a : ι') → β a) :=
    MeasurableEquiv.piCongrLeft (fun i ↦ β i) e
  refine Measure.pi_eq (fun s _ ↦ ?_) |>.symm
  rw [e_meas.measurableEmbedding.map_apply]
  let s' : (i : ι) → Set (β (e i)) := fun i ↦ s (e i)
  have : e_meas ⁻¹' Set.pi Set.univ s = Set.pi Set.univ s' := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, s']
    refine (e.forall_congr ?_).symm
    simp_rw [MeasurableEquiv.piCongrLeft_apply_apply e x _, implies_true]
  rw [this, Measure.pi_pi, Finset.prod_equiv e.symm]
  · simp only [Finset.mem_univ, implies_true]
  intro i _
  simp only [s']
  congr
  all_goals rw [e.apply_symm_apply]

-- todo: can we replace CountablyGenerated by CountableOrCountablyGenerated?
lemma kl_pi {ι : Type*} [hι : Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    [∀ i, CountablyGenerated (β i)] {μ ν : (i : ι) → Measure (β i)}
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    kl (Measure.pi μ) (Measure.pi ν) = ∑ i, kl (μ i) (ν i) := by
  refine Fintype.induction_empty_option (P := fun ι ↦ ∀ {β : ι → Type u_4}
    [(i : ι) → MeasurableSpace (β i)] [∀ (i : ι), CountablyGenerated (β i)]
    {μ ν : (i : ι) → Measure (β i)} [∀ (i : ι), IsProbabilityMeasure (μ i)]
    [∀ (i : ι), IsProbabilityMeasure (ν i)],
    kl (Measure.pi μ) (Measure.pi ν) = ∑ i : ι, kl (μ i) (ν i) ) ?_ ?_ ?_ ι
  · intro ι ι' hι' e h β _ _ μ ν _ _
    specialize h (β := fun i ↦ β (e i)) (μ := fun i ↦ μ (e i)) (ν := fun i ↦ ν (e i))
    let hι : Fintype ι := Fintype.ofEquiv _ e.symm
    rw [Fintype.sum_equiv e.symm _ (fun i ↦ kl (μ (e i)) (ν (e i))), ← h, kl_eq_fDiv, kl_eq_fDiv]
    let e_meas : ((b : ι) → β (e b)) ≃ᵐ ((a : ι') → β a) :=
      MeasurableEquiv.piCongrLeft (fun i ↦ β i) e
    have me := MeasurableEquiv.measurableEmbedding e_meas.symm
    convert (fDiv_map_measurableEmbedding me).symm
      <;> try {rw [← Measure.pi_map_piCongrLeft e, MeasurableEquiv.map_symm_map]}
      <;> infer_instance
    intro i
    rw [Equiv.apply_symm_apply]
  · intro β _ _ μ ν _ _
    rw [Measure.pi_of_empty, Measure.pi_of_empty, kl_self, Finset.univ_eq_empty, Finset.sum_empty]
  · intro ι hι ind_h β _ _ μ ν _ _
    specialize ind_h (β := fun i ↦ β i) (μ := fun i ↦ μ i) (ν := fun i ↦ ν i)
    have h : kl (Measure.pi μ) (Measure.pi ν) = kl ((Measure.pi (fun (i : ι) ↦ μ i)).prod
        (μ none)) ((Measure.pi (fun (i : ι) ↦ ν i)).prod (ν none)) := by
      rw [kl_eq_fDiv, kl_eq_fDiv]
      let e_meas : ((i : ι) → β (some i)) × β none ≃ᵐ ((i : Option ι) → β i) :=
        MeasurableEquiv.piOptionEquivProd β |>.symm
      have me := MeasurableEquiv.measurableEmbedding e_meas
      convert fDiv_map_measurableEmbedding me
        <;> try {exact Measure.pi_map_piOptionEquivProd _ |>.symm} <;> infer_instance
    rw [Fintype.sum_option, h, add_comm, ← ind_h]
    convert kl_prod_two <;> tauto <;> infer_instance

lemma kl_pi_const {ι : Type*} [hι : Fintype ι] [CountablyGenerated α]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    kl (Measure.pi (fun (_ : ι) ↦ μ)) (Measure.pi (fun (_ : ι) ↦ ν)) = hι.card * kl μ ν := by
  rw [kl_pi, Finset.sum_const, (Finset.card_eq_iff_eq_univ _).mpr rfl, EReal.nsmul_eq_mul]

end Tensorization

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : kernel α β}


lemma kl_comp_le_compProd [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    kl (μ ∘ₘ κ) (ν ∘ₘ η) ≤ kl (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simp_rw [kl_eq_fDiv]
  exact fDiv_comp_le_compProd μ ν κ η continuous_mul_log.stronglyMeasurable
    convexOn_mul_log continuous_mul_log.continuousOn

lemma kl_comp_left_le [Nonempty α] [StandardBorelSpace α] [CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    kl (μ ∘ₘ κ) (μ ∘ₘ η) ≤ condKL κ η μ := by
  rw [kl_eq_fDiv, condKL_eq_condFDiv]
  exact fDiv_comp_left_le μ κ η continuous_mul_log.stronglyMeasurable
    convexOn_mul_log continuous_mul_log.continuousOn

/--The **Data Processing Inequality** for the Kullback-Leibler divergence. -/
lemma kl_comp_right_le [Nonempty α] [StandardBorelSpace α] [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : kernel α β) [IsMarkovKernel κ] :
    kl (μ ∘ₘ κ) (ν ∘ₘ κ) ≤ kl μ ν := by
  simp_rw [kl_eq_fDiv]
  exact fDiv_comp_right_le μ ν κ continuous_mul_log.stronglyMeasurable
    convexOn_mul_log continuous_mul_log.continuousOn

end DataProcessingInequality

end ProbabilityTheory

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.KullbackLeibler.KullbackLeibler
import TestingLowerBounds.FDiv.CondFDivCompProdMeasure
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

section Conditional

variable {β γ : Type*} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {κ η : Kernel α β}

/--Equivalence between two possible versions of the first condition for the finiteness of the
conditional KL divergence, the second version is the preferred one.-/
lemma kl_ae_ne_top_iff : (∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ∞) ↔
    (∀ᵐ a ∂μ, κ a ≪ η a) ∧ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) := by
  simp_rw [kl_ne_top_iff, eventually_and]

/--Equivalence between two possible versions of the second condition for the finiteness of the
conditional KL divergence, the first version is the preferred one.-/
lemma integrable_kl_iff [IsMarkovKernel κ] [IsMarkovKernel η] (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ
      ↔ Integrable (fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)) μ := by
  have : ∀ᵐ a ∂μ, (kl (κ a) (η a)).toReal
      = ∫ b, llr (κ a) (η a) b ∂κ a + ((η a) Set.univ).toReal - ((κ a) Set.univ).toReal := by
    filter_upwards [h_ac] with a ha1
    rw [kl_toReal_of_ac ha1]
    simp
  rw [integrable_congr this]
  simp_rw [add_sub_assoc]
  rw [integrable_add_iff_integrable_left']
  simp

open Classical in
/--
Kullback-Leibler divergence between two kernels κ and η conditional to a measure μ.
It is defined as KL(κ, η | μ) := ∫ x, KL(κ x, η x) dμ.
-/
noncomputable
def condKL (κ η : Kernel α β) (μ : Measure α) : ℝ≥0∞ :=
  ∫⁻ a, kl (κ a) (η a) ∂μ

lemma condKL_eq_condFDiv [IsFiniteKernel κ] [IsFiniteKernel η] :
    condKL κ η μ = condFDiv klDivFun κ η μ := by
  simp_rw [condKL, condFDiv, kl_eq_fDiv]

section CondKLEq

lemma condKl_eq_lintegral_of_ae_ne_top (h1 : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ∞) :
    condKL κ η μ = ∫⁻ a, ENNReal.ofReal
      (∫ b, llr (κ a) (η a) b ∂κ a + ((η a) Set.univ).toReal - ((κ a) Set.univ).toReal) ∂μ := by
  simp_rw [condKL, kl]
  simp_rw [kl_ae_ne_top_iff] at h1
  refine lintegral_congr_ae ?_
  filter_upwards [h1.1, h1.2] with hx hx1 hx2
  simp [hx1, hx2]

lemma condKL_of_ae_ne_top_of_integrable [IsMarkovKernel κ] [IsMarkovKernel η]
    (h1 : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ∞)
    (h2 : Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = ENNReal.ofReal (μ[fun a ↦ (kl (κ a) (η a)).toReal]) := by
  rw [condKl_eq_lintegral_of_ae_ne_top h1]
  have : ∀ᵐ a ∂μ, (kl (κ a) (η a)).toReal
      = ∫ b, llr (κ a) (η a) b ∂κ a + ((η a) Set.univ).toReal - ((κ a) Set.univ).toReal := by
    rw [kl_ae_ne_top_iff] at h1
    filter_upwards [h1.1] with a ha1
    rw [kl_toReal_of_ac ha1]
    simp
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    refine integral_congr_ae ?_
    filter_upwards [this] with x hx
    rw [← hx]
  · rwa [← integrable_congr this]
  · filter_upwards [this] with x hx
    rw [← hx]
    exact ENNReal.toReal_nonneg

lemma condKL_of_ae_ac_of_ae_integrable_of_integrable [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a)
    (h_ae_int : ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
    (h_int : Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = ENNReal.ofReal (μ[fun a ↦ (kl (κ a) (η a)).toReal]) :=
  condKL_of_ae_ne_top_of_integrable (kl_ae_ne_top_iff.mpr ⟨h_ac, h_ae_int⟩) h_int

lemma condKL_of_ae_ac_of_ae_integrable_of_integrable' [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a)
    (h_ae_int : ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
    (h_int : Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = ENNReal.ofReal
      (μ[fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)
        + ((η a) Set.univ).toReal - ((κ a) Set.univ).toReal]) := by
  rw [condKL_of_ae_ac_of_ae_integrable_of_integrable h_ac h_ae_int h_int]
  congr 1
  apply integral_congr_ae
  filter_upwards [h_ac] with a ha1
  rw [kl_toReal_of_ac ha1]
  simp

@[simp]
lemma condKL_of_not_ae_ne_top [CountableOrCountablyGenerated α β]
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : ¬ ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ∞) :
    condKL κ η μ = ∞ := by
  rw [condKL]
  by_contra h'
  exact h ((ae_lt_top (measurable_kl _ _) h').mono fun x hx ↦ hx.ne)

@[simp]
lemma condKL_of_not_ae_ac [CountableOrCountablyGenerated α β] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : ¬ ∀ᵐ a ∂μ, κ a ≪ η a) :
    condKL κ η μ = ∞ := by
  rw [condKL_eq_condFDiv]
  exact condFDiv_of_not_ae_ac derivAtTop_klDivFun h

@[simp]
lemma condKL_of_not_ae_integrable [CountableOrCountablyGenerated α β]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h : ¬ ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) :
    condKL κ η μ = ∞ := by
  apply condKL_of_not_ae_ne_top
  rw [kl_ae_ne_top_iff]
  tauto

@[simp]
lemma condKL_of_not_integrable [CountableOrCountablyGenerated α β]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h : ¬ Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = ∞ := by
  by_cases h_top : ∀ᵐ x ∂μ, kl (κ x) (η x) ≠ ⊤
  swap; · exact condKL_of_not_ae_ne_top h_top
  rw [condKL]
  rwa [integrable_toReal_iff, ne_eq, not_not] at h
  · exact (measurable_kl _ _).aemeasurable
  · exact h_top

@[simp]
lemma condKL_of_not_integrable' [CountableOrCountablyGenerated α β]
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (h : ¬ Integrable (fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)) μ) :
    condKL κ η μ = ∞ := by
  by_cases h_ne_top : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ∞
  swap; · exact condKL_of_not_ae_ne_top h_ne_top
  apply condKL_of_not_integrable
  rwa [integrable_kl_iff (kl_ae_ne_top_iff.mp h_ne_top).1]

lemma condKL_toReal_of_ae_ac_of_ae_integrable [CountableOrCountablyGenerated α β]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a)
    (h_ae_int : ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) :
    (condKL κ η μ).toReal = μ[fun a ↦ (kl (κ a) (η a)).toReal] := by
  rw [condKL, integral_toReal]
  · exact (measurable_kl _ _).aemeasurable
  · filter_upwards [h_ac, h_ae_int] with x hx_ac hx_int
    rw [lt_top_iff_ne_top, kl_ne_top_iff]
    exact ⟨hx_ac, hx_int⟩

lemma condKL_eq_top_iff [CountableOrCountablyGenerated α β] [IsMarkovKernel κ] [IsMarkovKernel η] :
    condKL κ η μ = ∞
      ↔ ¬ (∀ᵐ a ∂μ, κ a ≪ η a) ∨ ¬ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
        ∨ ¬ Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ := by
  constructor <;> intro h
  · contrapose! h
    rw [condKL_of_ae_ac_of_ae_integrable_of_integrable h.1 h.2.1 h.2.2]
    exact ENNReal.ofReal_ne_top
  · rcases h with (h | h | h) <;>
      simp only [h, not_false_eq_true, condKL_of_not_ae_ac, condKL_of_not_ae_integrable,
        condKL_of_not_integrable]

lemma condKL_ne_top_iff [CountableOrCountablyGenerated α β] [IsMarkovKernel κ] [IsMarkovKernel η] :
    condKL κ η μ ≠ ∞
    ↔ (∀ᵐ a ∂μ, κ a ≪ η a) ∧ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
      ∧ Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ := by
  rw [ne_eq, condKL_eq_top_iff]
  push_neg
  rfl

lemma condKL_ne_top_iff' [CountableOrCountablyGenerated α β] [IsMarkovKernel κ] [IsMarkovKernel η] :
    condKL κ η μ ≠ ∞
      ↔ condKL κ η μ = ENNReal.ofReal (μ[fun a ↦ (kl (κ a) (η a)).toReal] : ℝ) := by
  constructor
  · rw [condKL_ne_top_iff]
    exact fun ⟨h1, h2, h3⟩ ↦ condKL_of_ae_ac_of_ae_integrable_of_integrable h1 h2 h3
  · intro h
    simp [h]

end CondKLEq

@[simp]
lemma condKL_self (κ : Kernel α β) (μ : Measure α) [IsFiniteKernel κ] : condKL κ κ μ = 0 := by
  simp [condKL]

@[simp]
lemma condKL_zero_left [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condKL 0 η μ = ∫⁻ a, η a Set.univ ∂μ := by simp [condKL_eq_condFDiv]

@[simp]
lemma condKL_zero_right [CountableOrCountablyGenerated α β]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h : ∃ᵐ a ∂μ, κ a ≠ 0) :
    condKL κ 0 μ = ∞ := by
  rw [condKL_of_not_ae_ac]
  simp [h]

@[simp]
lemma condKL_zero_measure : condKL κ η 0 = 0 := by simp [condKL]

@[simp]
lemma condKL_isEmpty_left [IsEmpty α] : condKL κ η μ = 0 := by
  have h : μ = 0 := by
    ext s
    exact Set.eq_empty_of_isEmpty s ▸ measure_empty
  exact h ▸ condKL_zero_measure

@[simp]
lemma condKL_const {ξ : Measure β} [IsFiniteMeasure ξ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    condKL (Kernel.const β μ) (Kernel.const β ν) ξ = (kl μ ν) * ξ .univ := by
  rw [condKL_eq_condFDiv, kl_eq_fDiv]
  exact condFDiv_const

lemma kl_fst_le [Nonempty β] [StandardBorelSpace β]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ.fst ν.fst ≤ kl μ ν := by
  simp_rw [kl_eq_fDiv]
  exact fDiv_fst_le _ _

lemma kl_snd_le [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ.snd ν.snd ≤ kl μ ν := by
  simp_rw [kl_eq_fDiv]
  exact fDiv_snd_le _ _

section CompProd

lemma le_kl_compProd [CountableOrCountablyGenerated α β] (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    kl μ ν ≤ kl (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simp_rw [kl_eq_fDiv]
  exact le_fDiv_compProd μ ν κ η

/- TODO: the following lemma may be generalized, infact the hypothesys of being markov kernels is
only used to prove that
`Integrable (fun x ↦ ∫ (y : β), ‖EReal.toReal (kl (κ (x, y)) (η (x, y)))‖ ∂ξ x) μ` is true,
given that `Integrable (fun x ↦ ∫ (y : β), EReal.toReal (kl (κ (x, y)) (η (x, y))) ∂ξ x` but if
the kernels are finite then the kl is bounded from below, so it should be still possible to conclude
the integrability of the first function, this would however require more work. -/
/-- This is to handle the case in `condKL_compProd_meas` when the lhs is ⊤, in this case the rhs is
'morally' also ⊤, so the equality holds, but actually in Lean the equality is not true, because of
how we handle the infinities in the integrals, so we have to make a separate lemma for this case. -/
lemma condKL_compProd_meas_eq_top [CountableOrCountablyGenerated (α × β) γ] [IsFiniteMeasure μ]
    {ξ : Kernel α β} [IsFiniteKernel ξ] {κ η : Kernel (α × β) γ}
    [IsMarkovKernel κ] [IsMarkovKernel η] :
    condKL κ η (μ ⊗ₘ ξ) = ∞
      ↔ ∫⁻ x, condKL (κ.snd' x) (η.snd' x) (ξ x) ∂μ = ∞ := by
  simp_rw [condKL_eq_condFDiv]
  rw [condFDiv_compProd_meas_eq_top]

-- TODO: find a better name
lemma condKL_compProd_meas [CountableOrCountablyGenerated (α × β) γ] [IsFiniteMeasure μ]
    {ξ : Kernel α β}
    [IsFiniteKernel ξ] {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η] :
    condKL κ η (μ ⊗ₘ ξ) = ∫⁻ x, condKL (κ.snd' x) (η.snd' x) (ξ x) ∂μ := by
  simp_rw [condKL_eq_condFDiv, condFDiv_compProd_meas]

lemma kl_compProd_left [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [∀ x, NeZero (κ x)] [IsFiniteKernel η] :
    kl (μ ⊗ₘ κ) (μ ⊗ₘ η) = condKL κ η μ := by
  rw [kl_eq_fDiv, condKL_eq_condFDiv]
  exact fDiv_compProd_left μ κ η

lemma kl_compProd_right (κ : Kernel α β) [CountableOrCountablyGenerated α β] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [IsMarkovKernel κ] :
    kl (μ ⊗ₘ κ) (ν ⊗ₘ κ) = kl μ ν := by
  rw [kl_eq_fDiv, kl_eq_fDiv]
  exact fDiv_compProd_right μ ν κ

section ChainRule

lemma klDivFun_mul {x y : ℝ≥0∞} (hx : x ≠ ∞) (hy : y ≠ ∞) :
    klDivFun (x * y) = (x * klDivFun y + y * klDivFun x) + 1 + x * y - x - y := by
  by_cases hx0 : x = 0
  · simp only [hx0, zero_mul, klDivFun_zero, mul_one, zero_add, add_zero, tsub_zero]
    exact (ENNReal.add_sub_cancel_left hy).symm
  by_cases hy0 : y = 0
  · simp only [hy0, mul_zero, klDivFun_zero, mul_one, zero_mul, add_zero, tsub_zero]
    exact (ENNReal.add_sub_cancel_left hx).symm
  rw [klDivFun_apply, klDivFun_apply hx, klDivFun_apply hy]
  swap; · exact ENNReal.mul_ne_top hx hy
  simp only [ENNReal.toReal_mul]
  have hx_real : x = ENNReal.ofReal x.toReal := by rw [ENNReal.ofReal_toReal hx]
  have hy_real : y = ENNReal.ofReal y.toReal := by rw [ENNReal.ofReal_toReal hy]
  suffices _ =
    ENNReal.ofReal x.toReal * ENNReal.ofReal (y.toReal * log y.toReal + 1 - y.toReal) +
          ENNReal.ofReal y.toReal * ENNReal.ofReal (x.toReal * log x.toReal + 1 - x.toReal) + 1 +
        ENNReal.ofReal x.toReal * ENNReal.ofReal y.toReal
        - ENNReal.ofReal x.toReal - ENNReal.ofReal y.toReal by
    simp_rw [hx_real.symm, hy_real.symm] at this
    exact this
  rw [log_mul]
  rw [← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_add, ← ENNReal.ofReal_add, ← ENNReal.ofReal_sub,
    ← ENNReal.ofReal_sub]
  · congr 1
    ring
  · positivity
  · positivity
  · refine add_nonneg
      (add_nonneg (mul_nonneg (by positivity) ?_) (mul_nonneg (by positivity) ?_)) zero_le_one
    · exact mul_log_add_one_sub_nonneg (by positivity)
    · exact mul_log_add_one_sub_nonneg (by positivity)
  · positivity
  · refine (add_nonneg (mul_nonneg (by positivity) ?_) (mul_nonneg (by positivity) ?_))
    · exact mul_log_add_one_sub_nonneg (by positivity)
    · exact mul_log_add_one_sub_nonneg (by positivity)
  · positivity
  · refine mul_nonneg (by positivity) ?_
    exact mul_log_add_one_sub_nonneg (by positivity)
  · refine mul_nonneg (by positivity) ?_
    exact mul_log_add_one_sub_nonneg (by positivity)
  · positivity
  · positivity
  · positivity
  · simp [ENNReal.toReal_eq_zero_iff, hx0, hx]
  · simp [ENNReal.toReal_eq_zero_iff, hy0, hy]

lemma todo1 {x y : ℝ≥0∞} (hx : x ≠ ∞) (hy : y ≠ ∞) :
    x ≤ x * klDivFun y + y * klDivFun x + 1 + x * y := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hx_real : x = ENNReal.ofReal x.toReal := by rw [ENNReal.ofReal_toReal hx]
  have hy_real : y = ENNReal.ofReal y.toReal := by rw [ENNReal.ofReal_toReal hy]
  suffices ENNReal.ofReal x.toReal
      ≤ ENNReal.ofReal x.toReal * klDivFun y + ENNReal.ofReal y.toReal * klDivFun x
        + 1 + ENNReal.ofReal x.toReal * ENNReal.ofReal y.toReal by
    simpa [← hx_real, ← hy_real]
  rw [klDivFun_apply hx, klDivFun_apply hy, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add,
    ← ENNReal.ofReal_add]
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [← sub_nonneg]
    calc 0
    _ ≤ (x.toReal * y.toReal) * log (x.toReal * y.toReal) + 1 - (x.toReal * y.toReal) :=
      mul_log_add_one_sub_nonneg (by positivity)
    _ = (x.toReal * (y.toReal * log y.toReal + 1 - y.toReal)
        + y.toReal * (x.toReal * log x.toReal + 1 - x.toReal) + 1
        + x.toReal * y.toReal - x.toReal) - y.toReal := by
      rw [log_mul]
      · ring
      · simp [ENNReal.toReal_eq_zero_iff, hx0, hx]
      · simp [ENNReal.toReal_eq_zero_iff, hy0, hy]
    _ ≤ x.toReal * (y.toReal * log y.toReal + 1 - y.toReal)
        + y.toReal * (x.toReal * log x.toReal + 1 - x.toReal) + 1
        + x.toReal * y.toReal - x.toReal := sub_le_self _ ENNReal.toReal_nonneg
  · refine add_nonneg
      (add_nonneg (mul_nonneg (by positivity) ?_) (mul_nonneg (by positivity) ?_)) zero_le_one
    · exact mul_log_add_one_sub_nonneg (by positivity)
    · exact mul_log_add_one_sub_nonneg (by positivity)
  · positivity
  · refine (add_nonneg (mul_nonneg (by positivity) ?_) (mul_nonneg (by positivity) ?_))
    · exact mul_log_add_one_sub_nonneg (by positivity)
    · exact mul_log_add_one_sub_nonneg (by positivity)
  · exact zero_le_one
  · refine mul_nonneg (by positivity) ?_
    exact mul_log_add_one_sub_nonneg (by positivity)
  · refine mul_nonneg (by positivity) ?_
    exact mul_log_add_one_sub_nonneg (by positivity)
  · positivity
  · positivity
  · positivity

lemma todo2 {x y : ℝ≥0∞} (hx : x ≠ ∞) (hy : y ≠ ∞) :
    y ≤ x * klDivFun y + y * klDivFun x + 1 + x * y - x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hx_real : x = ENNReal.ofReal x.toReal := by rw [ENNReal.ofReal_toReal hx]
  have hy_real : y = ENNReal.ofReal y.toReal := by rw [ENNReal.ofReal_toReal hy]
  suffices ENNReal.ofReal y.toReal
      ≤ ENNReal.ofReal x.toReal * klDivFun y + ENNReal.ofReal y.toReal * klDivFun x
        + 1 + ENNReal.ofReal x.toReal * ENNReal.ofReal y.toReal - ENNReal.ofReal x.toReal by
    simpa [← hx_real, ← hy_real]
  rw [klDivFun_apply hx, klDivFun_apply hy, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add,
    ← ENNReal.ofReal_add, ← ENNReal.ofReal_sub]
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [← sub_nonneg]
    calc 0
    _ ≤ (x.toReal * y.toReal) * log (x.toReal * y.toReal) + 1 - (x.toReal * y.toReal) :=
      mul_log_add_one_sub_nonneg (by positivity)
    _ = (x.toReal * (y.toReal * log y.toReal + 1 - y.toReal)
        + y.toReal * (x.toReal * log x.toReal + 1 - x.toReal) + 1
        + x.toReal * y.toReal - x.toReal) - y.toReal := by
      rw [log_mul]
      · ring
      · simp [ENNReal.toReal_eq_zero_iff, hx0, hx]
      · simp [ENNReal.toReal_eq_zero_iff, hy0, hy]
  · positivity
  · refine add_nonneg
      (add_nonneg (mul_nonneg (by positivity) ?_) (mul_nonneg (by positivity) ?_)) zero_le_one
    · exact mul_log_add_one_sub_nonneg (by positivity)
    · exact mul_log_add_one_sub_nonneg (by positivity)
  · positivity
  · refine (add_nonneg (mul_nonneg (by positivity) ?_) (mul_nonneg (by positivity) ?_))
    · exact mul_log_add_one_sub_nonneg (by positivity)
    · exact mul_log_add_one_sub_nonneg (by positivity)
  · exact zero_le_one
  · refine mul_nonneg (by positivity) ?_
    exact mul_log_add_one_sub_nonneg (by positivity)
  · refine mul_nonneg (by positivity) ?_
    exact mul_log_add_one_sub_nonneg (by positivity)
  · positivity
  · positivity
  · positivity

lemma lintegral_klDivFun_mul [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν)
    {x : ℝ≥0∞} (hx : x ≠ ∞) :
    ∫⁻ y, klDivFun (x * μ.rnDeriv ν y) ∂ν
      = x * ∫⁻ y, klDivFun (μ.rnDeriv ν y) ∂ν + klDivFun x := by
  have h_ne_top := μ.rnDeriv_ne_top ν
  have h_eq : ∀ᵐ y ∂ν, klDivFun (x * μ.rnDeriv ν y)
      = (x * klDivFun (μ.rnDeriv ν y) + (μ.rnDeriv ν y) * klDivFun x) + 1
        + x * μ.rnDeriv ν y - x - μ.rnDeriv ν y := by
    filter_upwards [h_ne_top] with y hy
    exact klDivFun_mul hx hy
  rw [lintegral_congr_ae h_eq, lintegral_sub, lintegral_sub, lintegral_add_right,
    lintegral_add_right, lintegral_add_right, lintegral_rnDeriv_mul hμν, lintegral_const_mul,
    Measure.lintegral_rnDeriv hμν, lintegral_const_mul, Measure.lintegral_rnDeriv hμν]
  · simp only [lintegral_const, measure_univ, mul_one]
    rw [ENNReal.add_sub_cancel_right hx, ENNReal.add_sub_cancel_right ENNReal.one_ne_top]
  · exact μ.measurable_rnDeriv ν
  · exact measurable_divFunction_rnDeriv
  · exact measurable_const.aemeasurable
  · exact (μ.measurable_rnDeriv ν).mul_const _
  · exact measurable_const
  · exact measurable_const.mul (μ.measurable_rnDeriv ν)
  · exact measurable_const
  · simp [hx]
  · filter_upwards [h_ne_top] with a ha
    exact todo1 hx ha
  · exact μ.measurable_rnDeriv ν
  · rw [Measure.lintegral_rnDeriv hμν]
    simp
  · filter_upwards [h_ne_top] with a ha
    exact todo2 hx ha

lemma lintegral_klDivFun_compProd [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫⁻ x, klDivFun ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x) ∂ν ⊗ₘ η
      = ∫⁻ a, klDivFun ((∂μ/∂ν) a) + (∂μ/∂ν) a * ∫⁻ b, klDivFun ((∂κ a/∂η a) b) ∂η a ∂ν := by
  have h_eq : ∫⁻ x, klDivFun ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x) ∂ν ⊗ₘ η
      = ∫⁻ a, ∫⁻ b, klDivFun ((∂μ/∂ν) a * (∂κ a/∂η a) b) ∂η a ∂ν := by
    have h := Kernel.rnDeriv_measure_compProd μ ν κ η
    rw [Measure.lintegral_compProd]
    swap; · exact measurable_divFunction_rnDeriv
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.ae_ae_of_ae_compProd h] with a ha
    refine lintegral_congr_ae ?_
    filter_upwards [ha, κ.rnDeriv_eq_rnDeriv_measure] with b hb hb2
    rw [hb, hb2]
  rw [h_eq]
  refine lintegral_congr_ae ?_
  have h_ac : ∀ᵐ a ∂ν, μ.rnDeriv ν a ≠ 0 → κ a ≪ η a :=
    Measure.ae_rnDeriv_ne_zero_imp_of_ae_aux hκη hμν
  filter_upwards [μ.rnDeriv_ne_top ν, h_ac] with a ha h_ac
  by_cases h_zero : μ.rnDeriv ν a = 0
  · simp [h_zero]
  · rw [lintegral_klDivFun_mul (h_ac h_zero) ha, add_comm]

/--The **chain rule** for the KL divergence.-/
lemma kl_compProd [CountableOrCountablyGenerated α β] [IsMarkovKernel κ] [IsMarkovKernel η]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl (μ ⊗ₘ κ) (ν ⊗ₘ η) = kl μ ν + condKL κ η μ := by
  by_cases h_prod : (μ ⊗ₘ κ) ≪ (ν ⊗ₘ η)
  swap
  · simp only [h_prod, not_false_eq_true, kl_of_not_ac]
    have h := Measure.absolutelyContinuous_compProd_iff.mpr.mt h_prod
    set_option push_neg.use_distrib true in push_neg at h
    rcases h with (hμν | hκη)
    · simp [hμν, not_false_eq_true, kl_of_not_ac]
    · simp [hκη, not_false_eq_true, condKL_of_not_ae_ac]
  have ⟨hμν, hκη⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_prod
  simp_rw [condKL, kl_eq_fDiv, fDiv_of_absolutelyContinuous hμν,
    fDiv_of_absolutelyContinuous h_prod]
  have : ∫⁻ a, fDiv klDivFun (κ a) (η a) ∂μ
      = ∫⁻ a, ∫⁻ x, klDivFun ((κ a).rnDeriv (η a) x) ∂η a ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hκη] with x hx
    rw [fDiv_of_absolutelyContinuous hx]
  rw [lintegral_klDivFun_compProd hμν hκη, this, lintegral_add_left, lintegral_rnDeriv_mul hμν]
  · exact (measurable_lintegral_f_rnDeriv κ η).aemeasurable
  · exact measurable_divFunction_rnDeriv

/--The **chain rule** for the KL divergence.-/
lemma kl_fst_add_condKL [StandardBorelSpace β] [Nonempty β] {μ ν : Measure (α × β)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ.fst ν.fst + condKL μ.condKernel ν.condKernel μ.fst = kl μ ν := by
  rw [← kl_compProd, μ.disintegrate, ν.disintegrate]

end ChainRule

/-TODO: this is just a thin wrapper around Kernel.integrable_llr_compProd_iff, so that that lemma
could be put in an outside file. But I have realised that the choice of having 2 instead of 2' as
the hp of choice about integrability here may be a bad one, because in cases like this one
it does not allow to move stuff outside this file, as it relies on the definition of kl.
Moreover in general it is the opposite choice to what is done in fDiv, and in fDiv the other choice
is much more convenient, because it allows to disregard the singular part inside the definition of
fDiv when talking about integrability. So I think it may be better to reverse this choice here,
changing the lemmas like condKL_ne_top_iff from 2 to 2'-/
lemma Kernel.integrable_llr_compProd_iff' [CountableOrCountablyGenerated β γ]
    {κ₁ η₁ : Kernel α β} {κ₂ η₂ : Kernel (α × β) γ} [IsFiniteKernel κ₁] [IsFiniteKernel η₁]
    [IsMarkovKernel κ₂] [IsMarkovKernel η₂] (a : α) (h_ac : (κ₁ ⊗ₖ κ₂) a ≪ (η₁ ⊗ₖ η₂) a) :
    Integrable (llr ((κ₁ ⊗ₖ κ₂) a) ((η₁ ⊗ₖ η₂) a)) ((κ₁ ⊗ₖ κ₂) a)
      ↔ Integrable (llr (κ₁ a) (η₁ a)) (κ₁ a)
        ∧ Integrable (fun b ↦ (kl (κ₂ (a, b)) (η₂ (a, b))).toReal) (κ₁ a)
        ∧ ∀ᵐ b ∂κ₁ a, Integrable (llr (κ₂ (a, b)) (η₂ (a, b))) (κ₂ (a, b)) := by
  convert Kernel.integrable_llr_compProd_iff a h_ac using 3
  simp_rw [← Kernel.snd'_apply]
  have h_ac' := Kernel.absolutelyContinuous_compProd_iff a |>.mp h_ac |>.2
  exact integrable_kl_iff h_ac'

lemma kl_compProd_kernel_of_ae_ac_of_ae_integrable [CountableOrCountablyGenerated β γ]
    {κ₁ η₁ : Kernel α β} {κ₂ η₂ : Kernel (α × β) γ} [IsFiniteKernel κ₁] [IsFiniteKernel η₁]
    [IsMarkovKernel κ₂] [IsMarkovKernel η₂] (h_ac : ∀ᵐ a ∂μ, (κ₁ ⊗ₖ κ₂) a ≪ (η₁ ⊗ₖ η₂) a)
    (h_ae_int : ∀ᵐ a ∂μ, Integrable (llr ((κ₁ ⊗ₖ κ₂) a) ((η₁ ⊗ₖ η₂) a)) ((κ₁ ⊗ₖ κ₂) a)) :
    ∀ᵐ a ∂μ, (kl ((κ₁ ⊗ₖ κ₂) a) ((η₁ ⊗ₖ η₂) a)).toReal
      = (kl (κ₁ a) (η₁ a)).toReal + ∫ b, (kl (κ₂ (a, b)) (η₂ (a, b))).toReal ∂κ₁ a := by
  simp only [eventually_congr (h_ac.mono (fun a h ↦ (Kernel.integrable_llr_compProd_iff' a h))),
    eventually_and] at h_ae_int
  simp only [Kernel.absolutelyContinuous_compProd_iff, eventually_and] at h_ac
  filter_upwards [h_ac.1, h_ac.2, h_ae_int.1, h_ae_int.2.1, h_ae_int.2.2] with a ha_ac₁ ha_ac₂
    ha_int₁ ha_int_kl₂ ha_int₂
  have h_snd_ne_top : condKL (κ₂.snd' a) (η₂.snd' a) (κ₁ a) ≠ ∞ := by
    apply condKL_ne_top_iff.mpr
    simp_rw [Kernel.snd'_apply]
    exact ⟨ha_ac₂, ⟨ha_int₂, ha_int_kl₂⟩⟩
  simp_rw [Kernel.compProd_apply_eq_compProd_snd', kl_compProd,
    condKL_ne_top_iff'.mp h_snd_ne_top, Kernel.snd'_apply]
  rw [ENNReal.toReal_add (kl_ne_top_iff.mpr ⟨ha_ac₁, ha_int₁⟩) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal]
  refine integral_nonneg fun x ↦ ENNReal.toReal_nonneg

lemma condKL_compProd_kernel_eq_top [CountableOrCountablyGenerated α β]
    [CountableOrCountablyGenerated α (β × γ)]
    [CountableOrCountablyGenerated (α × β) γ] {κ₁ η₁ : Kernel α β}
    {κ₂ η₂ : Kernel (α × β) γ} [IsMarkovKernel κ₁] [IsMarkovKernel η₁] [IsMarkovKernel κ₂]
    [IsMarkovKernel η₂] [SFinite μ] :
    condKL (κ₁ ⊗ₖ κ₂) (η₁ ⊗ₖ η₂) μ = ∞ ↔ condKL κ₁ η₁ μ = ∞ ∨ condKL κ₂ η₂ (μ ⊗ₘ κ₁) = ∞ := by
  by_cases h_empty : Nonempty α
  swap
  · replace h_empty := not_nonempty_iff.mp h_empty
    simp only [condKL_isEmpty_left]
    tauto
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  simp_rw [condKL_eq_top_iff, Measure.ae_compProd_iff (κ₂.measurableSet_absolutelyContinuous _)]
  by_cases h_ac : ∀ᵐ a ∂μ, (κ₁ ⊗ₖ κ₂) a ≪ (η₁ ⊗ₖ η₂) a
    <;> have h_ac' := h_ac
    <;> simp only [Kernel.absolutelyContinuous_compProd_iff, eventually_and, not_and_or] at h_ac'
    <;> simp only [h_ac, h_ac', not_false_eq_true, true_or, not_true, true_iff, false_or]
  swap; tauto
  rw [← Measure.ae_compProd_iff (κ₂.measurableSet_absolutelyContinuous _)] at h_ac'
  by_cases h_ae_int : ∀ᵐ a ∂μ, Integrable (llr ((κ₁ ⊗ₖ κ₂) a) ((η₁ ⊗ₖ η₂) a)) ((κ₁ ⊗ₖ κ₂) a)
    <;> have h_ae_int' := h_ae_int
    <;> simp only [eventually_congr (h_ac.mono (fun a h ↦ (Kernel.integrable_llr_compProd_iff' a h))),
      eventually_and, not_and_or] at h_ae_int'
    <;> simp only [h_ae_int, h_ae_int', not_false_eq_true, true_or, true_and, not_true, true_iff,
      false_or, not_and_or, ae_compProd_integrable_llr_iff h_ac'.2, Measure.integrable_compProd_iff
      (measurable_kl _ _).ennreal_toReal.stronglyMeasurable.aestronglyMeasurable]
  swap
  · by_cases h_int₁ : ∀ᵐ x ∂μ, Integrable (llr (κ₁ x) (η₁ x)) (κ₁ x)
    swap; tauto
    by_cases h_int₂ : ∀ᵐ a ∂μ, ∀ᵐ b ∂κ₁ a, Integrable (llr (κ₂ (a, b)) (η₂ (a, b))) (κ₂ (a, b))
    swap; tauto
    simp only [h_int₁, h_int₂, not_true_eq_false, false_or, or_false] at h_ae_int'
    right; right; left
    exact h_ae_int'
  simp only [norm_eq_abs, ENNReal.abs_toReal, ← not_and_or, not_iff_not]
  rw [integrable_congr (kl_compProd_kernel_of_ae_ac_of_ae_integrable h_ac h_ae_int), and_comm]
  simp_rw [add_comm (kl (κ₁ _) (η₁ _)).toReal]
  apply integrable_add_iff_of_nonneg
  · exact StronglyMeasurable.integral_kernel_prod_right' (κ := κ₁)
      ((measurable_kl κ₂ η₂).ennreal_toReal.stronglyMeasurable) |>.aestronglyMeasurable
  · filter_upwards with a using integral_nonneg (fun b ↦ ENNReal.toReal_nonneg)
  · filter_upwards with a using ENNReal.toReal_nonneg

-- todo: remove some [CountableOrCountablyGenerated _ _] hypotheses
lemma condKL_compProd_kernel [CountableOrCountablyGenerated α β]
    [CountableOrCountablyGenerated α (β × γ)]
    [CountableOrCountablyGenerated (α × β) γ] {κ₁ η₁ : Kernel α β}
    {κ₂ η₂ : Kernel (α × β) γ} [IsMarkovKernel κ₁] [IsMarkovKernel η₁] [IsMarkovKernel κ₂]
    [IsMarkovKernel η₂] [SFinite μ] :
    condKL (κ₁ ⊗ₖ κ₂) (η₁ ⊗ₖ η₂) μ = condKL κ₁ η₁ μ + condKL κ₂ η₂ (μ ⊗ₘ κ₁) := by
  by_cases h_empty : Nonempty α
  swap
  · replace h_empty := not_nonempty_iff.mp h_empty
    simp only [condKL_isEmpty_left, zero_add]
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  by_cases hp : condKL (κ₁ ⊗ₖ κ₂) (η₁ ⊗ₖ η₂) μ = ∞
  · rw [hp]
    rw [condKL_compProd_kernel_eq_top] at hp
    rcases hp with (h | h) <;> simp [h]
  obtain ⟨h1, h2⟩ := not_or.mp <| condKL_compProd_kernel_eq_top.mpr.mt hp
  rw [condKL_ne_top_iff'.mp hp, condKL_ne_top_iff'.mp h1, condKL_ne_top_iff'.mp h2]
  rw [← ne_eq, condKL_ne_top_iff] at h1 h2 hp
  rw [Measure.integral_compProd h2.2.2, ← ENNReal.ofReal_add]
  rotate_left
  · exact integral_nonneg fun _ ↦ ENNReal.toReal_nonneg
  · exact integral_nonneg fun _ ↦ integral_nonneg fun _ ↦ ENNReal.toReal_nonneg
  congr 1
  convert integral_add h1.2.2 (Integrable.integral_compProd' h2.2.2) using 1
  exact integral_congr_ae <| kl_compProd_kernel_of_ae_ac_of_ae_integrable hp.1 hp.2.1

end CompProd

end Conditional

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β}

lemma kl_comp_left_le [Nonempty α] [StandardBorelSpace α] [CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    kl (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condKL κ η μ := by
  rw [kl_eq_fDiv, condKL_eq_condFDiv]
  exact fDiv_comp_left_le μ κ η

end DataProcessingInequality

section Tensorization

variable {β : Type*} {mβ : MeasurableSpace β}

lemma kl_prod_two' [CountableOrCountablyGenerated α β] {ξ ψ : Measure β} [IsProbabilityMeasure ξ]
    [IsProbabilityMeasure ψ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]:
    kl (μ.prod ξ) (ν.prod ψ) = kl μ ν + kl ξ ψ * (μ .univ) := by
  simp only [← condKL_const, ← kl_compProd, Measure.compProd_const]

/--Tensorization property for KL divergence-/
lemma kl_prod_two [CountableOrCountablyGenerated α β] {ξ ψ : Measure β} [IsProbabilityMeasure ξ]
    [IsProbabilityMeasure ψ] [IsProbabilityMeasure μ] [IsFiniteMeasure ν] :
    kl (μ.prod ξ) (ν.prod ψ) = kl μ ν + kl ξ ψ := by
  simp only [kl_prod_two', measure_univ, EReal.coe_ennreal_one, mul_one]

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
  rw [kl_pi, Finset.sum_const, (Finset.card_eq_iff_eq_univ _).mpr rfl, nsmul_eq_mul]

end Tensorization

end ProbabilityTheory

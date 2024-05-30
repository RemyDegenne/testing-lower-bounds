/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.KullbackLeibler
import TestingLowerBounds.Hellinger
import Mathlib.Probability.Moments

/-!
# Rényi divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation


## Implementation details


-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

-- todo: move
lemma exp_mul_llr [SigmaFinite μ] [SigmaFinite ν] (hνμ : ν ≪ μ) :
    (fun x ↦ exp (a * llr μ ν x)) =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toReal ^ a := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν, Measure.rnDeriv_pos' hνμ] with x hx_lt_top hx_pos
  simp only [llr_def]
  have h_pos : 0 < ((∂μ/∂ν) x).toReal :=  ENNReal.toReal_pos hx_pos.ne' hx_lt_top.ne
  rw [← log_rpow h_pos, exp_log (rpow_pos_of_pos h_pos _)]

-- todo: move
lemma exp_mul_llr' [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (fun x ↦ exp (a * llr μ ν x)) =ᵐ[μ] fun x ↦ (μ.rnDeriv ν x).toReal ^ a := by
  filter_upwards [hμν <| Measure.rnDeriv_lt_top μ ν, Measure.rnDeriv_pos hμν]
    with x hx_lt_top hx_pos
  simp only [llr_def]
  have h_pos : 0 < ((∂μ/∂ν) x).toReal :=  ENNReal.toReal_pos hx_pos.ne' hx_lt_top.ne
  rw [← log_rpow h_pos, exp_log (rpow_pos_of_pos h_pos _)]

/-- Rényi divergence of order `a`.-/
noncomputable def renyiDiv (a : ℝ) (μ ν : Measure α) : EReal :=
  if a = 1 then kl μ ν
  else if hellingerDiv a μ ν ≠ ⊤
    then (a - 1)⁻¹ * log ((ν Set.univ).toReal + (a - 1) * (hellingerDiv a μ ν).toReal)
    else ⊤

@[simp]
lemma renyiDiv_zero (μ ν : Measure α) [SigmaFinite μ] [IsFiniteMeasure ν] :
    renyiDiv 0 μ ν = - log (ν {x | 0 < (∂μ/∂ν) x}).toReal := by
  rw [renyiDiv, if_neg zero_ne_one, if_pos]
  swap
  · rw [hellingerDiv_zero, ne_eq, EReal.coe_ennreal_eq_top_iff]
    exact measure_ne_top ν _
  simp [ne_eq, zero_sub, ← neg_inv, inv_one, EReal.coe_neg, EReal.coe_one, neg_mul, one_mul, ←
    sub_eq_add_neg, ite_not]
  rw [hellingerDiv_zero_toReal]
  norm_num

@[simp]
lemma renyiDiv_one (μ ν : Measure α) : renyiDiv 1 μ ν = kl μ ν := by
  rw [renyiDiv, if_pos rfl]

section TopAndBounds

lemma renyiDiv_eq_top_iff_hellingerDiv_eq_top' (ha_ne_one : a ≠ 1) :
    renyiDiv a μ ν = ⊤ ↔ hellingerDiv a μ ν = ⊤ := by
  simp only [renyiDiv, ha_ne_one, ↓reduceIte, ne_eq, ite_not, ite_eq_left_iff]
  rw [← EReal.coe_mul]
  simp only [EReal.coe_ne_top, imp_false, not_not]

lemma renyiDiv_eq_top_iff_hellingerDiv_eq_top [SigmaFinite μ] [SigmaFinite ν] :
    renyiDiv a μ ν = ⊤ ↔ hellingerDiv a μ ν = ⊤ := by
  by_cases ha : a = 1
  · rw [ha, renyiDiv_one, hellingerDiv_one]
  · exact renyiDiv_eq_top_iff_hellingerDiv_eq_top' ha

lemma renyiDiv_eq_top_iff_of_one_le (ha : 1 ≤ a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    renyiDiv a μ ν = ⊤
      ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∨ ¬ μ ≪ ν := by
  rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top, hellingerDiv_eq_top_iff_of_one_le ha]

lemma renyiDiv_ne_top_iff_of_one_le (ha : 1 ≤ a) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    renyiDiv a μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν := by
  rw [ne_eq, renyiDiv_eq_top_iff_hellingerDiv_eq_top, hellingerDiv_eq_top_iff_of_one_le ha]
  push_neg
  rfl

lemma renyiDiv_eq_top_iff_of_lt_one (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    renyiDiv a μ ν = ⊤ ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top, hellingerDiv_eq_top_iff_of_lt_one ha]

lemma renyiDiv_ne_top_iff_of_lt_one (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [SigmaFinite ν] :
    renyiDiv a μ ν ≠ ⊤ ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  rw [ne_eq, renyiDiv_eq_top_iff_hellingerDiv_eq_top, hellingerDiv_eq_top_iff_of_lt_one ha]
  push_neg
  rfl

lemma renyiDiv_ne_top_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν ≠ ⊤ := by
  rw [ne_eq, renyiDiv_eq_top_iff_hellingerDiv_eq_top]
  exact hellingerDiv_ne_top_of_lt_one ha_nonneg ha _ _

lemma renyiDiv_of_not_integrable' (ha_ne_one : a ≠ 1)
    (h_int : ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    renyiDiv a μ ν = ⊤ := by
  rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top' ha_ne_one]
  by_contra h
  exact h (hellingerDiv_of_not_integrable h_int)

lemma renyiDiv_of_not_integrable [IsFiniteMeasure μ] [SigmaFinite ν]
    (h_int : ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    renyiDiv a μ ν = ⊤ := by
  rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top]
  by_contra h
  exact h (hellingerDiv_of_not_integrable h_int)

lemma renyiDiv_of_one_le_of_not_ac (ha : 1 ≤ a) (hμν : ¬ μ ≪ ν)
    [SigmaFinite μ] [SigmaFinite ν] :
    renyiDiv a μ ν = ⊤ := by
  by_cases ha_one : a = 1
  · rw [ha_one, renyiDiv_one]
    exact kl_of_not_ac hμν
  replace ha : 1 < a := lt_of_le_of_ne ha fun h ↦ ha_one h.symm
  rw [renyiDiv, if_neg ha.ne', if_neg]
  rw [hellingerDiv_ne_top_iff_of_one_le ha.le]
  push_neg
  exact fun _ ↦ hμν

lemma renyiDiv_of_lt_one' (ha_lt_one : a < 1) [IsFiniteMeasure μ] [SigmaFinite ν]
    (h_int : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    renyiDiv a μ ν
      = (a - 1)⁻¹ * log ((ν Set.univ).toReal + (a - 1) * (hellingerDiv a μ ν).toReal) := by
  rw [renyiDiv, if_neg ha_lt_one.ne,
    if_pos ((hellingerDiv_ne_top_iff_of_lt_one ha_lt_one _ _).mpr h_int)]

lemma renyiDiv_of_lt_one (ha_nonneg : 0 ≤ a) (ha_lt_one : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν
      = (a - 1)⁻¹ * log ((ν Set.univ).toReal + (a - 1) * (hellingerDiv a μ ν).toReal) := by
  rw [renyiDiv_of_lt_one' ha_lt_one]
  exact integrable_hellingerFun_rnDeriv_of_lt_one ha_nonneg ha_lt_one

lemma renyiDiv_of_one_lt_of_integrable_of_ac (ha_one_lt : 1 < a) [IsFiniteMeasure μ] [SigmaFinite ν]
    (h_int : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) (hμν : μ ≪ ν) :
    renyiDiv a μ ν
      = (a - 1)⁻¹ * log ((ν Set.univ).toReal + (a - 1) * (hellingerDiv a μ ν).toReal) := by
  rw [renyiDiv, if_neg ha_one_lt.ne',
    if_pos ((hellingerDiv_ne_top_iff_of_one_le ha_one_lt.le _ _).mpr ⟨h_int, hμν⟩)]

end TopAndBounds

section IntegralForm

/-- The Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `ν`. -/
lemma renyiDiv_eq_log_integral (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν) := by
  rw [renyiDiv_of_lt_one ha_pos.le ha μ ν]
  congr
  simp_rw [hellingerDiv_toReal_of_lt_one ha_pos ha, mul_sub, ← mul_assoc,
    mul_inv_cancel (sub_neg.mpr ha).ne, one_mul]
  norm_num

/-- The Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `ν`.
If `a < 1`, use `renyiDiv_eq_log_integral` instead. -/
lemma renyiDiv_eq_log_integral_of_ne_top (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : renyiDiv a μ ν ≠ ⊤) :
    renyiDiv a μ ν = (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν) := by
  cases lt_or_gt_of_ne ha_ne_one with
  | inl ha => exact renyiDiv_eq_log_integral ha_pos ha
  | inr ha =>
    have h_ne_top : hellingerDiv a μ ν ≠ ⊤ := by
      rwa [ne_eq, ← renyiDiv_eq_top_iff_hellingerDiv_eq_top]
    rw [renyiDiv_ne_top_iff_of_one_le ha.le] at h
    rw [renyiDiv_of_one_lt_of_integrable_of_ac ha h.1 h.2]
    congr
    rw [hellingerDiv_eq_integral_of_ne_top' ha_pos.ne' ha_ne_one h_ne_top]
    rw [EReal.toReal_sub, EReal.toReal_mul, EReal.toReal_coe, EReal.toReal_coe, mul_sub, ← mul_assoc,
      mul_inv_cancel, one_mul, EReal.toReal_mul, EReal.toReal_coe, ← mul_assoc, mul_inv_cancel (by linarith), one_mul]
    · simp
    · linarith
    · rw [← EReal.coe_mul]
      exact EReal.coe_ne_top _
    · rw [← EReal.coe_mul]
      exact EReal.coe_ne_bot _
    · simp [measure_ne_top, EReal.mul_eq_top]
    · simp [measure_ne_top, EReal.mul_eq_bot]

/-- If `μ ≪ ν`, the Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `μ`. -/
lemma renyiDiv_eq_log_integral' (ha_pos : 0 < a) (ha : a < 1) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    renyiDiv a μ ν = (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x).toReal ^ (a - 1) ∂μ) := by
  rw [renyiDiv_eq_log_integral ha_pos ha, integral_rpow_rnDeriv ha_pos ha.ne]
  congr 3
  refine integral_congr_ae ?_
  filter_upwards [Measure.inv_rnDeriv hμν] with x hx
  rw [← hx, Pi.inv_apply, ENNReal.toReal_inv, inv_rpow ENNReal.toReal_nonneg,
    ← rpow_neg ENNReal.toReal_nonneg, neg_sub]

/-- If `μ ≪ ν`, the Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `μ`.
If `a < 1`, use `renyiDiv_eq_log_integral'` instead. -/
lemma renyiDiv_eq_log_integral_of_ne_top' (ha_pos : 0 < a) (ha : a ≠ 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμν : μ ≪ ν) (h : renyiDiv a μ ν ≠ ⊤) :
    renyiDiv a μ ν = (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x).toReal ^ (a - 1) ∂μ) := by
  rw [renyiDiv_eq_log_integral_of_ne_top ha_pos ha, integral_rpow_rnDeriv ha_pos ha]
  congr 3
  refine integral_congr_ae ?_
  filter_upwards [Measure.inv_rnDeriv hμν] with x hx
  rw [← hx, Pi.inv_apply, ENNReal.toReal_inv, inv_rpow ENNReal.toReal_nonneg,
    ← rpow_neg ENNReal.toReal_nonneg, neg_sub]
  congr

end IntegralForm

lemma renyiDiv_symm' (ha_pos : 0 < a) (ha : a < 1) (h_eq : μ Set.univ = ν Set.univ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (1 - a) * renyiDiv a μ ν = a * renyiDiv (1 - a) ν μ := by
  rw [renyiDiv_of_lt_one ha_pos.le ha, renyiDiv_of_lt_one _ _]
  rotate_left
  · linarith
  · linarith
  simp only [sub_sub_cancel_left, neg_mul]
  rw [← mul_assoc, ← mul_assoc]
  have h : (1 - a) * hellingerDiv a μ ν = a * hellingerDiv (1 - a) ν μ :=
    hellingerDiv_symm' ha_pos ha h_eq
  have : (1 - (a : EReal)) * ↑(a - 1)⁻¹ = -1 := by
    norm_cast
    rw [← neg_neg (1 - a), neg_sub, neg_mul, mul_inv_cancel]
    · simp
    · linarith
  rw [this, ← EReal.coe_mul, inv_neg, mul_neg, mul_inv_cancel ha_pos.ne']
  simp only [EReal.coe_neg, EReal.coe_one, one_mul]
  congr 5
  · exact h_eq.symm
  rw [← EReal.toReal_coe a, ← EReal.toReal_mul, EReal.toReal_coe a, ← h, EReal.toReal_mul,
    ← neg_mul]
  congr 1
  norm_cast
  rw [EReal.toReal_coe, neg_sub]

lemma renyiDiv_symm (ha_pos : 0 < a) (ha : a < 1)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (1 - a) * renyiDiv a μ ν = a * renyiDiv (1 - a) ν μ :=
  renyiDiv_symm' ha_pos ha (by simp)

-- todo: `ν ≪ μ` is necessary (?) due to the llr being 0 when `(∂μ/∂ν) x = 0`.
-- In that case, `exp (llr μ ν x) = 1 ≠ 0 = (∂μ/∂ν) x`.
lemma coe_cgf_llr (ha_pos : 0 < a) (ha : a < 1) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hνμ : ν ≪ μ) :
    cgf (llr μ ν) ν a = (a - 1) * renyiDiv a μ ν := by
  rw [renyiDiv_eq_log_integral ha_pos ha, ← mul_assoc]
  have : ((a : EReal) - 1) * ↑(a - 1)⁻¹ = 1 := by
    norm_cast
    rw [mul_inv_cancel]
    linarith
  rw [this, one_mul, cgf, mgf]
  congr 2
  exact integral_congr_ae (exp_mul_llr hνμ)

lemma cgf_llr (ha_pos : 0 < a) (ha : a < 1) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hνμ : ν ≪ μ) :
    cgf (llr μ ν) ν a = (a - 1) * (renyiDiv a μ ν).toReal := by
  have : (a - 1) * (renyiDiv a μ ν).toReal = ((a - 1) * renyiDiv a μ ν).toReal := by
    rw [EReal.toReal_mul, ← EReal.coe_one, ← EReal.coe_sub, EReal.toReal_coe]
  rw [this, ← coe_cgf_llr ha_pos ha hνμ, EReal.toReal_coe]

lemma coe_cgf_llr' (ha_pos : 0 < a) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : renyiDiv (1 + a) μ ν ≠ ⊤) :
    cgf (llr μ ν) μ a = a * renyiDiv (1 + a) μ ν := by
  have hμν : μ ≪ ν := by
    rw [renyiDiv_ne_top_iff_of_one_le] at h
    · exact h.2
    · linarith
  rw [renyiDiv_eq_log_integral_of_ne_top' _ _ hμν h, ← mul_assoc]
  rotate_left
  · linarith
  · linarith
  simp only [add_sub_cancel_left]
  have : (a : EReal) * ↑a⁻¹ = 1 := by
    norm_cast
    rw [mul_inv_cancel]
    linarith
  rw [this, one_mul, cgf, mgf]
  congr 2
  exact integral_congr_ae (exp_mul_llr' hμν)

lemma cgf_llr' (ha_pos : 0 < a) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : renyiDiv (1 + a) μ ν ≠ ⊤) :
    cgf (llr μ ν) μ a = a * (renyiDiv (1 + a) μ ν).toReal := by
  have : a * (renyiDiv (1 + a) μ ν).toReal = (a * renyiDiv (1 + a) μ ν).toReal := by
    rw [EReal.toReal_mul, EReal.toReal_coe]
  rw [this, ← coe_cgf_llr' ha_pos h, EReal.toReal_coe]

section RenyiMeasure

/-- Density of the Rényi measure `renyiMeasure a μ ν` with respect to `μ + ν`. -/
noncomputable
def renyiDensity (a : ℝ) (μ ν : Measure α) (x : α) : ℝ≥0∞ :=
  ((∂μ/∂(μ + ν)) x) ^ a * ((∂ν/∂(μ + ν)) x) ^ (1 - a)
    * ENNReal.ofReal (exp (- (a - 1) * (renyiDiv a μ ν).toReal))

/-- Tilted measure of `μ` with respect to `ν` parametrized by `a`. -/
noncomputable
def renyiMeasure (a : ℝ) (μ ν : Measure α) : Measure α :=
  (μ + ν).withDensity (renyiDensity a μ ν)

end RenyiMeasure

section Conditional

variable {β γ : Type*} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {κ η : kernel α β}


/-- Rényi divergence between two kernels κ and η conditional to a measure μ.
It is defined as `Rₐ(κ, η | μ) := Rₐ(μ ⊗ₘ κ, μ ⊗ₘ η)`. -/
noncomputable
def condRenyiDiv (a : ℝ) (κ η : kernel α β) (μ : Measure α) : EReal :=
  renyiDiv a (μ ⊗ₘ κ) (μ ⊗ₘ η)

--Maybe this can be stated in a nicer way, but I didn't find a way to do it. It's probably good enough to use `condRenyiDiv_of_lt_one`.
lemma condRenyiDiv_zero (κ η : kernel α β) (μ : Measure α) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    condRenyiDiv 0 κ η μ = - log ((μ ⊗ₘ η) {x | 0 < (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x}).toReal := by
  rw [condRenyiDiv, renyiDiv_zero]

@[simp]
lemma condRenyiDiv_one [CountableOrCountablyGenerated α β] (κ η : kernel α β) (μ : Measure α)
    [IsMarkovKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv 1 κ η μ = condKL κ η μ := by
  rw [condRenyiDiv, renyiDiv_one, kl_compProd_left]

section TopAndBounds

lemma condRenyiDiv_eq_top_iff_of_one_le [CountableOrCountablyGenerated α β] (ha : 1 ≤ a)
    (κ η : kernel α β) (μ : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ = ⊤
      ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
        ∨ ¬Integrable (fun x ↦ ∫ (b : β), hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ
        ∨ ¬ ∀ᵐ x ∂μ, κ x ≪ η x := by
  rw [condRenyiDiv, renyiDiv_eq_top_iff_of_one_le ha,
    kernel.Measure.absolutelyContinuous_compProd_right_iff, integrable_f_rnDeriv_compProd_right_iff
      (stronglyMeasurable_hellingerFun (by linarith)) (convexOn_hellingerFun (by linarith))]
  tauto

lemma condRenyiDiv_ne_top_iff_of_one_le [CountableOrCountablyGenerated α β] (ha : 1 ≤ a)
    (κ η : kernel α β) (μ : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ ≠ ⊤
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
        ∧ Integrable (fun x ↦ ∫ (b : β), hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ
        ∧ ∀ᵐ x ∂μ, κ x ≪ η x := by
  rw [ne_eq, condRenyiDiv_eq_top_iff_of_one_le ha]
  push_neg
  rfl

lemma condRenyiDiv_eq_top_iff_of_lt_one [CountableOrCountablyGenerated α β] (ha_nonneg : 0 ≤ a)
    (ha : a < 1) (κ η : kernel α β) (μ : Measure α)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ = ⊤
    ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
      ∨ ¬Integrable (fun x ↦ ∫ (b : β), hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ := by
  rw [condRenyiDiv, renyiDiv_eq_top_iff_of_lt_one ha, integrable_f_rnDeriv_compProd_right_iff
      (stronglyMeasurable_hellingerFun (by linarith)) (convexOn_hellingerFun (by linarith))]
  tauto

lemma condRenyiDiv_ne_top_iff_of_lt_one [CountableOrCountablyGenerated α β] (ha_nonneg : 0 ≤ a)
    (ha : a < 1) (κ η : kernel α β) (μ : Measure α)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ ≠ ⊤
    ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
      ∧ Integrable (fun x ↦ ∫ (b : β), hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ := by
  rw [ne_eq, condRenyiDiv_eq_top_iff_of_lt_one ha_nonneg ha]
  push_neg
  rfl

lemma condRenyiDiv_ne_top_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) (κ η : kernel α β)
    (μ : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ ≠ ⊤ := by
  rw [condRenyiDiv, ne_eq, renyiDiv_eq_top_iff_hellingerDiv_eq_top]
  exact hellingerDiv_ne_top_of_lt_one ha_nonneg ha _ _

lemma condRenyiDiv_of_not_ae_integrable [CountableOrCountablyGenerated α β] (ha_nonneg : 0 ≤ a)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
    (h_int : ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))) :
    condRenyiDiv a κ η μ = ⊤ := by
  by_cases ha : a < 1
  · have := integrable_hellingerFun_rnDeriv_of_lt_one ha_nonneg ha (μ := μ ⊗ₘ κ) (ν := μ ⊗ₘ η)
    rw [integrable_f_rnDeriv_compProd_right_iff
      (stronglyMeasurable_hellingerFun (by linarith)) (convexOn_hellingerFun (by linarith))] at this
    exfalso
    exact h_int this.1
  · rw [condRenyiDiv_eq_top_iff_of_one_le (le_of_not_lt ha)]
    left
    exact h_int

lemma condRenyiDiv_of_not_integrable [CountableOrCountablyGenerated α β] (ha_nonneg : 0 ≤ a)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
    (h_int : ¬Integrable (fun x ↦ ∫ (b : β), hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ) :
    condRenyiDiv a κ η μ = ⊤ := by
  by_cases ha : a < 1
  · have := integrable_hellingerFun_rnDeriv_of_lt_one ha_nonneg ha (μ := μ ⊗ₘ κ) (ν := μ ⊗ₘ η)
    rw [integrable_f_rnDeriv_compProd_right_iff
      (stronglyMeasurable_hellingerFun (by linarith)) (convexOn_hellingerFun (by linarith))] at this
    exfalso
    exact h_int this.2
  · rw [condRenyiDiv_eq_top_iff_of_one_le (le_of_not_lt ha)]
    exact Or.inr (Or.inl h_int)

lemma condRenyiDiv_of_one_le_of_not_ac [CountableOrCountablyGenerated α β] (ha : 1 ≤ a)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] (h_ac : ¬ ∀ᵐ x ∂μ, κ x ≪ η x) :
    condRenyiDiv a κ η μ = ⊤ := by
  rw [condRenyiDiv_eq_top_iff_of_one_le ha]
  exact Or.inr (Or.inr h_ac)

lemma condRenyiDiv_of_lt_one [CountableOrCountablyGenerated α β] (ha_nonneg : 0 ≤ a)
    (ha_lt_one : a < 1) (κ η : kernel α β) (μ : Measure α) [IsFiniteKernel κ] [∀ x, NeZero (κ x)]
    [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ = (a - 1)⁻¹
      * log (((μ ⊗ₘ η) Set.univ).toReal + (a - 1) * (condHellingerDiv a κ η μ).toReal) := by
  rw [condRenyiDiv, renyiDiv_of_lt_one ha_nonneg ha_lt_one, hellingerDiv_compProd_left ha_nonneg _]

lemma condRenyiDiv_of_one_lt_of_ac [CountableOrCountablyGenerated α β] (ha_one_lt : 1 < a)
    (κ η : kernel α β) (μ : Measure α) [IsFiniteKernel κ] [∀ x, NeZero (κ x)]
    [IsFiniteKernel η] [IsFiniteMeasure μ]
    (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
    (h_ac : ∀ᵐ x ∂μ, (κ x) ≪ (η x))
    (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condRenyiDiv a κ η μ = (a - 1)⁻¹
      * log (((μ ⊗ₘ η) Set.univ).toReal + (a - 1) * (condHellingerDiv a κ η μ).toReal) := by
  have ha_pos : 0 < a := by linarith
  rw [condRenyiDiv, renyiDiv_of_one_lt_of_integrable_of_ac ha_one_lt _ _,
    hellingerDiv_compProd_left ha_pos.le _]
  · refine (integrable_f_rnDeriv_compProd_right_iff (stronglyMeasurable_hellingerFun ha_pos.le)
      (convexOn_hellingerFun ha_pos.le)).mpr ⟨h_int, ?_⟩
    apply (integrable_hellingerDiv_iff h_int fun _ ↦ h_ac).mp
    exact (integrable_hellingerDiv_iff' ha_pos ha_one_lt.ne' h_int fun _ ↦ h_ac).mpr h_int'
  · exact kernel.Measure.absolutelyContinuous_compProd_iff.mpr ⟨fun _ a ↦ a, h_ac⟩

end TopAndBounds


end Conditional

end ProbabilityTheory

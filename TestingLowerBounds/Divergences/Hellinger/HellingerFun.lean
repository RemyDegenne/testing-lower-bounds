/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Notation
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import TestingLowerBounds.ForMathlib.RnDeriv
import TestingLowerBounds.Divergences.KullbackLeibler.KullbackLeibler
import TestingLowerBounds.IntegrableFRNDeriv

/-!
# Hellinger divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details

How to define a `DivFunction` from a real function `f`:
- prove that the function is convex, that `f 1 = 0` and `rightDeriv f 1 = 0`.
  For the right derivative, consider proving that the derivative is 0, if it exists.
- if applicable, prove that `f` is continuous at zero
- find the limit of `f` at +∞
- useful lemma: `f` is nonnegative
- useful lemma: `0 ≤ ∫ x, f (μ.rnDeriv ν x) ∂ν`. Simplify the integral to get other inequalities.

Then use `DivFunction.ofReal`.

-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

--TODO: try to add these attributes to fun_prop? how to do this?
attribute [fun_prop] Measure.measurable_rnDeriv Measurable.ennreal_toReal

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

section IntegralRPowRnDeriv

-- todo: rename and move.
lemma integral_rpow_rnDeriv (ha_pos : 0 < a) (ha : a ≠ 1) [SigmaFinite μ] [SigmaFinite ν] :
    ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν = ∫ x, ((∂ν/∂μ) x).toReal ^ (1 - a) ∂μ := by
  let p := ∂μ/∂(μ + ν)
  let q := ∂ν/∂(μ + ν)
  calc ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν
    = ∫ x, ((p/q) x).toReal ^ a ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [μ.rnDeriv_eq_div ν] with x hx
        simp only [hx, Pi.div_apply, p, q]
  _ = ∫ x, (q x).toReal * ((p/q) x).toReal ^ a ∂(μ + ν) := by
        rw [← integral_rnDeriv_smul (_ : ν ≪ μ + ν)]
        · simp
        · rw [add_comm]
          exact Measure.AbsolutelyContinuous.rfl.add_right μ
  _ = ∫ x, (p x).toReal * ((q/p) x).toReal ^ (1 - a) ∂(μ + ν) := by
        refine integral_congr_ae ?_
        filter_upwards [μ.rnDeriv_lt_top (μ + ν), ν.rnDeriv_lt_top (μ + ν)]
          with x hp_top hq_top
        by_cases hp : p x = 0
        · simp [hp, ha_pos.ne']
        by_cases hq : q x = 0
        · simp only [hq, ENNReal.zero_toReal, Pi.div_apply, zero_mul, ENNReal.zero_div,
            zero_eq_mul, le_refl]
          refine Or.inr ?_
          rw [zero_rpow]
          rwa [ne_eq, sub_eq_zero, Eq.comm]
        simp only [Pi.div_apply, ENNReal.toReal_div, div_eq_mul_inv, ENNReal.toReal_mul,
          mul_rpow ENNReal.toReal_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg), ENNReal.toReal_inv,
          inv_rpow ENNReal.toReal_nonneg, ← rpow_neg ENNReal.toReal_nonneg, neg_sub]
        rw [mul_comm, mul_assoc, mul_comm _ ((p x).toReal ^ (a - 1)), ← mul_assoc (p x).toReal]
        congr
        · have : a = 1 + (a - 1) := by abel
          conv_lhs => rw [this]
          rw [rpow_add, rpow_one]
          rw [ENNReal.toReal_pos_iff]
          exact ⟨zero_le'.lt_of_ne' hp, hp_top⟩
        · rw [mul_comm, rpow_sub, rpow_one, rpow_neg ENNReal.toReal_nonneg, div_eq_mul_inv]
          rw [ENNReal.toReal_pos_iff]
          exact ⟨zero_le'.lt_of_ne' hq, hq_top⟩
  _ = ∫ x, ((q/p) x).toReal ^ (1 - a) ∂μ := by
        rw [← integral_rnDeriv_smul (_ : μ ≪ μ + ν)]
        · simp
        · exact Measure.AbsolutelyContinuous.rfl.add_right ν
  _ = ∫ x, ((∂ν/∂μ) x).toReal ^ (1 - a) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [ν.rnDeriv_eq_div μ] with x hx
        rw [add_comm] at hx
        simp only [hx, Pi.div_apply, p, q]

lemma integrable_rpow_rnDeriv_iff [SigmaFinite ν] [SigmaFinite μ] (hμν : μ ≪ ν) (ha : 0 < a) :
    Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) μ
      ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ (1 + a)) ν := by
  rw [← integrable_rnDeriv_smul_iff hμν]
  refine integrable_congr ?_
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx
  simp only [smul_eq_mul]
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [h_zero, ENNReal.zero_toReal, zero_mul]
    rw [zero_rpow]
    linarith
  · rw [rpow_add (ENNReal.toReal_pos h_zero hx), rpow_one]

lemma rightDeriv_rpow {x : ℝ} (hx : x ≠ 0) :
    rightDeriv (fun x ↦ x ^ a) x = a * x ^ (a - 1) := by
  refine rightDeriv_of_hasDerivAt ?_
  exact Real.hasDerivAt_rpow_const (Or.inl hx)

lemma integrable_rpow_rnDeriv_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν := by
  rw [← integrable_neg_iff]
  refine integrable_f_rnDeriv_of_derivAtTop_ne_top (f := fun y ↦ - y ^ a) μ ν ?_ ?_ ?_
  · exact (Measurable.stronglyMeasurable (by fun_prop)).neg
  · exact (concaveOn_rpow ha_nonneg ha.le).neg
  · suffices derivAtTop (fun y ↦ -y ^ a) = 0 by simp [this]
    refine derivAtTop_of_tendsto_nhds ?_
    rw [_root_.rightDeriv_neg, ← neg_zero]
    refine Tendsto.neg ?_
    have : rightDeriv (fun x ↦ x ^ a) =ᶠ[atTop] fun x ↦ a * x ^ (a - 1) := by
      filter_upwards [eventually_ne_atTop 0] with x hx
      rw [rightDeriv_rpow hx]
    rw [tendsto_congr' this, ← mul_zero a]
    refine Tendsto.const_mul _ ?_
    have : (fun (x : ℝ) ↦ x ^ (a - 1)) = (fun x ↦ x ^ (- (1 - a))) := by ext x; simp
    rw [this]
    exact tendsto_rpow_neg_atTop (by linarith)

lemma integral_rpow_rnDeriv_nonneg : 0 ≤ ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν := by
  apply integral_nonneg
  intro x
  simp only [Pi.zero_apply, ENNReal.toReal_nonneg, rpow_nonneg]

lemma integral_fun_rnDeriv_eq_zero_iff_mutuallySingular [SigmaFinite μ] [SigmaFinite ν]
    {f : ℝ≥0∞ → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) (hf_zero : ∀ x, f x = 0 ↔ x = 0 ∨ x = ⊤)
    (h_int : Integrable (f ∘ (∂μ/∂ν)) ν) :
    ∫ x, f ((∂μ/∂ν) x) ∂ν = 0 ↔ μ ⟂ₘ ν := by
  rw [← Measure.rnDeriv_eq_zero, integral_eq_zero_iff_of_nonneg (fun _ ↦ hf_nonneg _) h_int]
  apply Filter.eventually_congr
  filter_upwards [μ.rnDeriv_ne_top ν] with x hx
  simp only [Pi.zero_apply, hf_zero, hx, or_false]

lemma integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular [SigmaFinite μ] [SigmaFinite ν]
    (ha_zero : a ≠ 0) (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) :
    ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν = 0 ↔ μ ⟂ₘ ν := by
  have h_nonneg : ∀ (x : ℝ≥0∞), 0 ≤ x.toReal ^ a := by
    intro x
    simp only [Pi.zero_apply, ENNReal.toReal_nonneg, rpow_nonneg]
  refine integral_fun_rnDeriv_eq_zero_iff_mutuallySingular h_nonneg (fun x ↦ ?_) h_int
  rw [rpow_eq_zero ENNReal.toReal_nonneg ha_zero, ENNReal.toReal_eq_zero_iff]

lemma integral_rpow_rnDeriv_pos_iff_not_mutuallySingular [SigmaFinite μ] [SigmaFinite ν]
    (ha_zero : a ≠ 0) (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) :
    0 < ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν ↔ ¬ μ ⟂ₘ ν := by
  rw [← integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular ha_zero h_int]
  push_neg
  exact LE.le.gt_iff_ne integral_rpow_rnDeriv_nonneg

lemma integral_rpow_rnDeriv_smul_left [SigmaFinite μ] [SigmaFinite ν] (c : ℝ≥0) :
    ∫ x, ((∂(c • μ)/∂ν) x).toReal ^ a ∂ν = c ^ a * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν := by
  rw [← integral_mul_left]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_smul_left' μ ν c] with x hx
  rw [← mul_rpow NNReal.zero_le_coe ENNReal.toReal_nonneg, hx, Pi.smul_apply, ENNReal.toReal_smul]
  rfl

lemma integral_rpow_rnDeriv_smul_right [SigmaFinite μ] [SigmaFinite ν] (c : ℝ≥0)
    (ha : c = 0 → a ≠ 1) :
    ∫ x, ((∂μ/∂(c • ν)) x).toReal ^ a ∂(c • ν) = c ^ (1 - a) * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν := by
  by_cases hc : c = 0; · simp [hc, zero_rpow <| sub_ne_zero_of_ne (ha hc).symm]
  rw [integral_smul_nnreal_measure, ← integral_mul_left, NNReal.smul_def, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_smul_right' μ ν hc] with x hx
  rw [hx, Pi.smul_apply, ENNReal.toReal_smul, smul_eq_mul, NNReal.smul_def, smul_eq_mul,
    mul_rpow NNReal.zero_le_coe ENNReal.toReal_nonneg, NNReal.coe_inv, inv_rpow NNReal.zero_le_coe,
    ← mul_assoc, mul_eq_mul_right_iff]
  left
  rw [rpow_sub, rpow_one, div_eq_mul_inv]
  exact NNReal.coe_pos.mpr <| pos_iff_ne_zero.mpr hc

lemma tendsto_mul_log_integral_rpow_rnDeriv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_int : Integrable (llr μ ν) μ) :
    Tendsto (fun a ↦ (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν)) (𝓝[<] 1)
      (𝓝 (∫ x, llr μ ν x ∂μ)) := by
  sorry

lemma log_integral_rpow_rnDeriv_sub_log_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_int : Integrable (llr μ ν) μ) :
    0 ≤ log (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν)
      - log ((1 - a) * (ν .univ).toReal + a * (μ .univ).toReal) := by
  sorry

lemma tendsto_mul_log_integral_rpow_rnDeriv' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_int : Integrable (llr μ ν) μ) :
    Tendsto (fun a ↦ (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν)
                    - (a - 1)⁻¹ * log ((1 - a) * (ν .univ).toReal + a * (μ .univ).toReal))
      (𝓝[<] 1)
      (𝓝 ((μ .univ).toReal⁻¹ * ∫ x, llr μ ν x ∂μ - log ((μ .univ).toReal / (ν .univ).toReal))) := by
  sorry

lemma tendsto_mul_log_integral_rpow_rnDeriv'' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_int : Integrable (llr μ ν) μ) (hμν : μ ≪ ν) :
    Tendsto (fun a ↦ (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν)
                    - (a - 1)⁻¹ * log ((1 - a) * (ν .univ).toReal + a * (μ .univ).toReal))
      (𝓝[<] 1)
      (𝓝 ((μ .univ).toReal⁻¹ * ((kl μ ν).toReal + (μ .univ).toReal - (ν .univ).toReal)
            - log ((μ .univ).toReal / (ν .univ).toReal))) := by
  rw [kl_toReal hμν h_int]
  convert tendsto_mul_log_integral_rpow_rnDeriv' h_int
  ring

end IntegralRPowRnDeriv

section HellingerFun

/--Hellinger function, defined as `x ↦ (a - 1)⁻¹ * (x ^ a - 1)` for `a ∈ (0, 1) ∪ (1, + ∞)`.
At `0` the function is obtained by contiuity and is the indicator function of `{0}`. At `1` it is
defined as `x ↦ x * log x`, because in this way we obtain that the Hellinger divergence at `1`
conincides with the KL divergence, which is natural for continuity reasons.-/
noncomputable
def hellingerFun (a : ℝ) : ℝ → ℝ :=
  if a = 0 then fun x ↦ if x = 0 then 1 else 0
  else if a = 1 then fun x ↦ x * log x + 1 - x
  else fun x ↦ (a - 1)⁻¹ * (x ^ a - 1 - a * (x - 1))

@[simp]
lemma hellingerFun_zero : hellingerFun 0 = fun x ↦ if x = 0 then 1 else 0 := by
  ext x
  simp [hellingerFun]

lemma hellingerFun_zero' : hellingerFun 0 = fun x ↦ 0 ^ x := by
  ext x
  by_cases h : x = 0 <;> simp [hellingerFun, h]

lemma hellingerFun_zero'' : hellingerFun 0 = Set.indicator {0} 1 := by
  ext x
  by_cases h : x = 0 <;> simp [hellingerFun_zero, h]

@[simp]
lemma hellingerFun_one : hellingerFun 1 = fun x ↦ x * log x + 1 - x := by
  ext x
  simp [hellingerFun]

lemma hellingerFun_of_ne_zero_of_ne_one (ha_zero : a ≠ 0) (ha_one : a ≠ 1) :
    hellingerFun a = fun x ↦ (a - 1)⁻¹ * (x ^ a - 1 - a * (x - 1)) := by
  ext x
  simp [hellingerFun, ha_zero, ha_one]

lemma continuous_rpow_const (ha_nonneg : 0 ≤ a) : Continuous fun (x : ℝ) ↦ x ^ a := by
  rw [continuous_iff_continuousAt]
  exact fun _ ↦ continuousAt_rpow_const _ _ (Or.inr ha_nonneg)

lemma continuous_hellingerFun (ha_pos : 0 < a) : Continuous (hellingerFun a) := by
  by_cases ha_eq : a = 1
  · rw [ha_eq, hellingerFun_one]
    fun_prop
  rw [hellingerFun, if_neg ha_pos.ne', if_neg ha_eq]
  refine continuous_const.mul ?_
  refine ((continuous_rpow_const ha_pos.le).sub continuous_const).sub ?_
  fun_prop

lemma stronglyMeasurable_hellingerFun (ha_nonneg : 0 ≤ a) :
    StronglyMeasurable (hellingerFun a) := by
  cases  (lt_or_eq_of_le ha_nonneg) with
  | inl ha_pos => exact (continuous_hellingerFun ha_pos).stronglyMeasurable
  | inr ha_eq =>
    rw [← ha_eq, hellingerFun_zero'']
    measurability

@[simp]
lemma hellingerFun_apply_one_eq_zero : hellingerFun a 1 = 0 := by
  by_cases ha_one : a = 1
  · simp [ha_one, hellingerFun_one]
  by_cases ha_zero : a = 0
  · simp [ha_zero, hellingerFun_zero]
  simp [hellingerFun, ha_one, ha_zero]

@[simp]
lemma hellingerFun_apply_zero : hellingerFun a 0 = 1 := by
  by_cases ha_zero : a = 0
  · simp [ha_zero, hellingerFun_zero]
  by_cases ha_one : a = 1
  · simp [ha_one, hellingerFun_one]
  simp only [hellingerFun, ha_zero, ↓reduceIte, ha_one, ne_eq, not_false_eq_true, zero_rpow,
    zero_sub, mul_neg, mul_one, sub_neg_eq_add]
  rw [add_comm, ← sub_eq_add_neg, inv_mul_cancel₀]
  rwa [sub_ne_zero]

lemma convexOn_hellingerFun (ha_pos : 0 ≤ a) : ConvexOn ℝ (Set.Ici 0) (hellingerFun a) := by
  by_cases ha_zero : a = 0
  · refine convexOn_iff_slope_mono_adjacent.mpr ?_
    simp only [convex_Ici, Set.mem_Ici, smul_eq_mul, true_and, hellingerFun_zero, ha_zero]
    intro x y z hx _ hxy hyz
    simp only [(lt_of_le_of_lt hx hxy).ne', ↓reduceIte, zero_sub,
      (gt_trans hyz <| lt_of_le_of_lt hx hxy).ne', sub_self, zero_div, div_nonpos_iff,
      Left.nonneg_neg_iff, tsub_le_iff_right, zero_add, Left.neg_nonpos_iff, sub_nonneg]
    exact Or.inr ⟨by positivity, by linarith⟩
  replace ha_pos := ha_pos.lt_of_ne fun h ↦ ha_zero h.symm
  rcases (lt_trichotomy a 1) with (ha | ha | ha)
  · have : hellingerFun a = - (fun x ↦ (1 - a)⁻¹ • (x ^ a - 1 - a * (x - 1))) := by
      ext x
      rw [Pi.neg_apply, hellingerFun_of_ne_zero_of_ne_one ha_pos.ne' ha.ne, smul_eq_mul, ← neg_mul,
        neg_inv, neg_sub]
    rw [this]
    refine (((Real.concaveOn_rpow ha_pos.le ha.le).sub
      (convexOn_const _ (convex_Ici 0))).sub ?_).smul (by simp [ha.le]) |>.neg
    exact ((convexOn_id (convex_Ici 0)).sub (concaveOn_const _ (convex_Ici 0))).smul ha_pos.le
  · simp only [hellingerFun, ha, one_ne_zero, ↓reduceIte]
    exact convexOn_mul_log_add_one_sub
  · simp_rw [hellingerFun, ← smul_eq_mul, if_neg ha_pos.ne', if_neg ha.ne']
    refine ((convexOn_rpow ha.le).sub (concaveOn_const _ (convex_Ici 0))).sub ?_ |>.smul
      (by simp [ha.le])
    exact ((concaveOn_id (convex_Ici 0)).sub (convexOn_const _ (convex_Ici 0))).smul ha_pos.le

lemma hasDerivAt_hellingerFun (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (hellingerFun a)
      (if a = 0 then 0
      else if a = 1 then log x
      else (a - 1)⁻¹ * a * (x ^ (a - 1) - 1)) x := by
  split_ifs with h1 h2
  · rw [h1, hellingerFun_zero]
    refine HasDerivAt.congr_of_eventuallyEq (f := fun _ ↦ 0) (hasDerivAt_const _ _) ?_
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [hy]
  · simp only [h2, hellingerFun_one]
    exact hasDerivAt_mul_log_add_one_sub hx
  · rw [hellingerFun_of_ne_zero_of_ne_one h1 h2, mul_assoc]
    refine HasDerivAt.const_mul _ ?_
    rw [mul_sub]
    refine HasDerivAt.sub ?_ ?_
    · exact (Real.hasDerivAt_rpow_const (Or.inl hx)).sub_const _
    · exact ((hasDerivAt_id x).sub_const _).const_mul _

lemma leftDeriv_hellingerFun (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    leftDeriv (hellingerFun a) x =
      if a = 0 then 0
      else if a = 1 then log x
      else (a - 1)⁻¹ * a * (x ^ (a - 1) - 1) :=
  leftDeriv_of_hasDerivAt (hasDerivAt_hellingerFun a hx)

lemma rightDeriv_hellingerFun (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    rightDeriv (hellingerFun a) x =
      if a = 0 then 0
      else if a = 1 then log x
      else (a - 1)⁻¹ * a * (x ^ (a - 1) - 1) :=
  rightDeriv_of_hasDerivAt (hasDerivAt_hellingerFun a hx)

@[simp]
lemma leftDeriv_hellingerFun_one :
    leftDeriv (hellingerFun a) 1 = 0 := by
  simp [leftDeriv_hellingerFun]

@[simp]
lemma rightDeriv_hellingerFun_one :
    rightDeriv (hellingerFun a) 1 = 0 := by
  simp [rightDeriv_hellingerFun]

lemma hellingerFun_nonneg (ha : 0 ≤ a) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ hellingerFun a x := by
  rcases hx.eq_or_lt with rfl | hx; · simp
  refine ConvexOn.nonneg_of_todo ?_ hellingerFun_apply_one_eq_zero rightDeriv_hellingerFun_one hx
  exact (convexOn_hellingerFun ha).subset (Set.Ioi_subset_Ici le_rfl) (convex_Ioi _)

lemma tendsto_rightDeriv_hellingerFun_atTop_of_one_lt (ha : 1 < a) :
    Tendsto (rightDeriv (hellingerFun a)) atTop atTop := by
  have : rightDeriv (hellingerFun a) =ᶠ[atTop] fun x ↦ (a - 1)⁻¹ * a * (x ^ (a - 1) - 1) := by
    filter_upwards [eventually_ne_atTop 0] with x hx
    rw [rightDeriv_hellingerFun _ hx]
    simp [(zero_lt_one.trans ha).ne', ha.ne']
  rw [tendsto_congr' this]
  simp_rw [mul_assoc, tendsto_const_mul_atTop_iff]
  have h1 : ¬ a < 0 := by linarith
  have h2 : ¬ a < 1 := by linarith
  simp only [inv_pos, sub_pos, ha, zero_lt_one.trans ha, true_and, h1, false_and, or_false,
    inv_neg'', sub_neg, h2]
  refine tendsto_atTop_add_const_right atTop (-1) ?_
  exact tendsto_rpow_atTop (by linarith)

lemma tendsto_rightDeriv_hellingerFun_atTop_of_lt_one (ha : a < 1) :
    Tendsto (rightDeriv (hellingerFun a)) atTop (𝓝 (a * (1 - a)⁻¹)) := by
  by_cases ha_zero : a = 0
  · simp only [ha_zero, sub_zero, inv_one, mul_one]
    have : rightDeriv (hellingerFun 0) =ᶠ[atTop] fun _ ↦ 0 := by
      filter_upwards [eventually_ne_atTop 0] with x hx
      rw [rightDeriv_hellingerFun _ hx]
      simp
    rw [tendsto_congr' this]
    exact tendsto_const_nhds
  · have : rightDeriv (hellingerFun a) =ᶠ[atTop] fun x ↦ (a - 1)⁻¹ * a * (x ^ (a - 1) - 1) := by
      filter_upwards [eventually_ne_atTop 0] with x hx
      rw [rightDeriv_hellingerFun _ hx]
      simp [ha_zero, ha.ne]
    rw [tendsto_congr' this]
    have h_eq : (fun x ↦ (a - 1)⁻¹ * a * (x ^ (a - 1) - 1))
        = (fun x ↦ a * (1 - x ^ (a - 1)) * (1 - a)⁻¹) := by
      ext x
      rw [mul_assoc, mul_comm, mul_assoc, mul_assoc]
      congr 1
      rw [← neg_sub 1 a, inv_neg, mul_neg, neg_sub, ← neg_mul, neg_sub]
    rw [h_eq]
    refine Tendsto.mul_const _ ?_
    simp_rw [mul_sub, mul_one]
    suffices Tendsto (fun k ↦ a - a * k ^ (a - 1)) atTop (𝓝 (a - a * 0)) by
      simpa using this
    refine Tendsto.const_sub _ ?_
    refine Tendsto.const_mul _ ?_
    have : (fun (x : ℝ) ↦ x ^ (a - 1)) = (fun x ↦ x ^ (-(1 - a))) := by ext x; simp
    rw [this]
    exact tendsto_rpow_neg_atTop (by linarith)

lemma derivAtTop_hellingerFun_of_one_lt (ha : 1 < a) : derivAtTop (hellingerFun a) = ⊤ :=
   derivAtTop_of_tendsto_atTop <| tendsto_rightDeriv_hellingerFun_atTop_of_one_lt ha

-- lemma derivAtTop_hellingerFun_of_one_le (ha : 1 ≤ a) :
--     derivAtTop (hellingerFun a) = ⊤ := by
--   by_cases ha_eq : a = 1
--   · simp only [hellingerFun, ha, ha_eq, one_ne_zero, ↓reduceIte, derivAtTop_mul_log]
--   · exact derivAtTop_hellingerFun_of_one_lt <| lt_of_le_of_ne ha fun h ↦ ha_eq h.symm

lemma derivAtTop_hellingerFun_of_lt_one (ha : a < 1) :
    derivAtTop (hellingerFun a) = (a * (1 - a)⁻¹) :=
  derivAtTop_of_tendsto_nhds <| tendsto_rightDeriv_hellingerFun_atTop_of_lt_one ha

lemma integrable_hellingerFun_one_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    Integrable (fun x ↦ hellingerFun 1 ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (llr μ ν) μ := by
  simp only [hellingerFun_one]
  rw [integrable_mul_log_add_one_sub_iff hμν]

lemma integrable_hellingerFun_iff_integrable_rpow (ha_one : a ≠ 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν := by
  by_cases ha_zero : a = 0
  · simp_rw [ha_zero, hellingerFun_zero'', rpow_zero, integrable_const, iff_true,
      ← Set.indicator_comp_right fun x ↦ ((∂μ/∂ν) x).toReal, Set.preimage, Set.mem_singleton_iff,
      Pi.one_comp]
    refine (integrable_indicator_iff ?_).mpr ?_
    · apply measurableSet_eq_fun <;> fun_prop
    · exact integrableOn_const.mpr (Or.inr (measure_lt_top ν _))
  rw [hellingerFun_of_ne_zero_of_ne_one ha_zero ha_one, integrable_const_mul_iff]
  swap; · simp [sub_eq_zero, ha_one]
  simp_rw [sub_eq_add_neg, add_assoc, ← sub_eq_add_neg]
  rw [integrable_add_iff_integrable_left']
  refine (integrable_const _).add (((Integrable.sub ?_ (integrable_const _)).const_mul _).neg)
  exact Measure.integrable_toReal_rnDeriv

lemma integrable_hellingerFun_zero [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x ↦ hellingerFun 0 ((∂μ/∂ν) x).toReal) ν := by
  simp_rw [integrable_hellingerFun_iff_integrable_rpow zero_ne_one, rpow_zero]
  exact integrable_const _

lemma integrable_hellingerFun_rnDeriv_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  rw [integrable_hellingerFun_iff_integrable_rpow ha.ne]
  exact integrable_rpow_rnDeriv_of_lt_one ha_nonneg ha

lemma integral_hellingerFun_of_pos_of_ne_one_of_integrable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1) (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν) :
    ∫ x, hellingerFun a (μ.rnDeriv ν x).toReal ∂ν
     = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * ∫ x, (μ.rnDeriv ν x).toReal ∂ν := by
  calc ∫ x, hellingerFun a (μ.rnDeriv ν x).toReal ∂ν
  _ = (a - 1)⁻¹ * ∫ x, ((μ.rnDeriv ν x).toReal ^ a - 1 - a * ((μ.rnDeriv ν x).toReal - 1)) ∂ν := by
    rw [← integral_mul_left]
    simp_rw [hellingerFun_of_ne_zero_of_ne_one ha_pos.ne' ha_ne]
  _ = (a - 1)⁻¹ * ∫ x, ((μ.rnDeriv ν x).toReal ^ a + (a - 1) - a * (μ.rnDeriv ν x).toReal) ∂ν := by
    congr with x
    ring
  _ = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
      + (ν .univ).toReal + (1 - a)⁻¹ * a * ∫ x, (μ.rnDeriv ν x).toReal ∂ν := by
    rw [integral_sub, integral_add, integral_const, smul_eq_mul, mul_comm _ (a - 1),
      integral_mul_left, mul_sub, mul_add, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀, one_mul,
      sub_eq_add_neg]
    · congr
      rw [mul_assoc, ← neg_mul, neg_inv, neg_sub, ← mul_assoc]
    · rwa [sub_ne_zero]
    · exact h_int
    · exact integrable_const _
    · exact h_int.add (integrable_const _)
    · exact Measure.integrable_toReal_rnDeriv.const_mul _

lemma integral_hellingerFun_of_pos_of_ne_one_of_integrable_of_ac
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1) (h_int : Integrable (fun x ↦ (μ.rnDeriv ν x).toReal ^ a) ν)
    (hμν : μ ≪ ν) :
    ∫ x, hellingerFun a (μ.rnDeriv ν x).toReal ∂ν
     = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * (μ .univ).toReal := by
  rw [integral_hellingerFun_of_pos_of_ne_one_of_integrable ha_pos ha_ne h_int,
    Measure.integral_toReal_rnDeriv hμν]

lemma integral_hellingerFun_of_pos_of_lt_one [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_lt : a < 1) :
    ∫ x, hellingerFun a (μ.rnDeriv ν x).toReal ∂ν
     = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * ∫ x, (μ.rnDeriv ν x).toReal ∂ν :=
  integral_hellingerFun_of_pos_of_ne_one_of_integrable ha_pos ha_lt.ne
    (integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha_lt)

lemma integral_hellingerFun_of_pos_of_lt_one_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_lt : a < 1) (hμν : μ ≪ ν) :
    ∫ x, hellingerFun a (μ.rnDeriv ν x).toReal ∂ν
     = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * (μ .univ).toReal := by
  rw [integral_hellingerFun_of_pos_of_lt_one ha_pos ha_lt, Measure.integral_toReal_rnDeriv hμν]

-- todo name
-- rewriting of `0 ≤ ∫ x, hellingerFun a (μ.rnDeriv ν x).toReal ∂ν`.
lemma integral_hellingerFun_rnDeriv_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_lt : a < 1) :
    0 ≤ (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * ∫ x, (μ.rnDeriv ν x).toReal ∂ν := by
  calc 0
  _ ≤ ∫ x, hellingerFun a (μ.rnDeriv ν x).toReal ∂ν := by
    refine integral_nonneg fun x ↦ hellingerFun_nonneg ha_pos.le ENNReal.toReal_nonneg
  _ = (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
      + (ν .univ).toReal + (1 - a)⁻¹ * a * ∫ x, (μ.rnDeriv ν x).toReal ∂ν :=
    integral_hellingerFun_of_pos_of_lt_one ha_pos ha_lt

-- todo name
lemma integral_hellingerFun_rnDeriv_nonneg_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ha_pos : 0 < a) (ha_lt : a < 1) (hμν : μ ≪ ν) :
    0 ≤ (a - 1)⁻¹ * ∫ x, (μ.rnDeriv ν x).toReal ^ a ∂ν
        + (ν .univ).toReal + (1 - a)⁻¹ * a * (μ .univ).toReal := by
  refine (integral_hellingerFun_rnDeriv_nonneg ha_pos ha_lt (μ := μ) (ν := ν)).trans_eq ?_
  rw [Measure.integral_toReal_rnDeriv hμν]

end HellingerFun

end ProbabilityTheory

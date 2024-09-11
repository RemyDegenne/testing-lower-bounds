/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!

# Change of measure inequalities

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## TODO

The lemma names in this file are bad.

-/

open MeasureTheory Real

open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν ν' : Measure α} {s : Set α}

lemma setLIntegral_nnnorm_exp_neg_llr_le [SigmaFinite ν] [SigmaFinite μ]
    (hμν : μ ≪ ν) (s : Set α) :
    ∫⁻ a in s, ‖rexp (-llr μ ν a)‖₊ ∂μ ≤ ν s := by
  set t := toMeasurable ν s
  have ht : MeasurableSet t := measurableSet_toMeasurable ν s
  calc ∫⁻ a in s, ‖rexp (-llr μ ν a)‖₊ ∂μ
      ≤ ∫⁻ a in t, ‖rexp (-llr μ ν a)‖₊ ∂μ := lintegral_mono_set (subset_toMeasurable ν s)
    _ = ∫⁻ a in t, ‖(ν.rnDeriv μ a).toReal‖₊ ∂μ := by
        refine setLIntegral_congr_fun ht ?_
        filter_upwards [exp_neg_llr hμν] with x hx _
        rw [hx]
    _ = ∫⁻ a in t, ν.rnDeriv μ a ∂μ := by
        refine setLIntegral_congr_fun ht ?_
        filter_upwards [ν.rnDeriv_ne_top μ] with x hx _
        rw [← ofReal_norm_eq_coe_nnnorm]
        simp [hx]
    _ ≤ ν t := Measure.setLIntegral_rnDeriv_le t
    _ = ν s := measure_toMeasurable s

lemma integrableOn_exp_neg_llr [SigmaFinite ν] [SigmaFinite μ] (hμν : μ ≪ ν) (hνs : ν s ≠ ∞) :
    IntegrableOn (fun x ↦ exp (- llr μ ν x)) s μ := by
  constructor
  · refine AEStronglyMeasurable.restrict ?_
    refine StronglyMeasurable.aestronglyMeasurable ?_
    exact (measurable_llr _ _).neg.exp.stronglyMeasurable
  · rw [hasFiniteIntegral_def]
    calc ∫⁻ a in s, ‖rexp (-llr μ ν a)‖₊ ∂μ
      ≤ ν s := setLIntegral_nnnorm_exp_neg_llr_le hμν s
    _ < ∞ := hνs.lt_top

lemma setIntegral_exp_neg_llr_le [SigmaFinite ν] [SigmaFinite μ] (hμν : μ ≪ ν) (hνs : ν s ≠ ∞) :
    ∫ x in s, exp (- llr μ ν x) ∂μ ≤ (ν s).toReal := by
  set t := toMeasurable ν s with ht_eq
  have ht : MeasurableSet t := measurableSet_toMeasurable ν s
  have hνt : ν t ≠ ∞ := by rwa [ht_eq, measure_toMeasurable s]
  calc ∫ x in s, exp (- llr μ ν x) ∂μ
    ≤ ∫ x in t, exp (- llr μ ν x) ∂μ := by
        refine setIntegral_mono_set ?_ ?_ (subset_toMeasurable _ _).eventuallyLE
        · exact integrableOn_exp_neg_llr hμν hνt
        · exact ae_of_all _ (fun _ ↦ (exp_pos _).le)
  _ = ∫ x in t, exp (llr ν μ x) ∂μ := by
        refine setIntegral_congr_ae ht ?_
        filter_upwards [neg_llr hμν] with x hx _ using by rw [← hx]; rfl
  _ = ∫ x in t, (ν.rnDeriv μ x).toReal ∂μ := by
        refine setIntegral_congr_ae ht ?_
        filter_upwards [exp_llr ν μ, Measure.rnDeriv_pos' hμν] with x hx hx_pos _
        simp [hx, hx_pos.ne']
  _ ≤ (ν t).toReal := Measure.setIntegral_toReal_rnDeriv_le hνt
  _ = (ν s).toReal := by rw [measure_toMeasurable s]

-- todo: if `0 < c` then `hμc` can be deducted from an integrability assumption on `llr μ ν`.
lemma measure_sub_le_measure_mul_exp [SigmaFinite μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (s : Set α) (c : ℝ) (hμc : μ {x | c < llr μ ν x} ≠ ∞) :
    (μ s).toReal - (μ {x | c < llr μ ν x}).toReal ≤ (ν s).toReal * exp c := by
  by_cases hμs : μ s = ∞
  · simp only [hμs, ENNReal.top_toReal, gt_iff_lt, zero_sub]
    calc - (μ {x | c < llr μ ν x}).toReal
      ≤ 0 := by simp
    _ ≤ (ν s).toReal * exp c := by positivity
  rw [← div_le_iff₀ (exp_pos _), div_eq_mul_inv, ← exp_neg]
  calc ((μ s).toReal - (μ {x | c < llr μ ν x}).toReal) * rexp (-c)
    ≤ (μ (s \ {x | c < llr μ ν x})).toReal * rexp (-c) := by
        gcongr
        refine (ENNReal.le_toReal_sub hμc).trans ?_
        rw [ENNReal.toReal_le_toReal]
        · exact le_measure_diff
        · exact (tsub_le_self.trans_lt (Ne.lt_top hμs)).ne
        · exact ((measure_mono Set.inter_subset_left).trans_lt (Ne.lt_top hμs)).ne
  _ = (μ (s ∩ {x | llr μ ν x ≤ c})).toReal * rexp (-c) := by congr with x; simp
  _ = ∫ _ in s ∩ {x | llr μ ν x ≤ c}, exp (- c) ∂μ := by rw [setIntegral_const _, smul_eq_mul]
  _ ≤ ∫ x in s ∩ {x | llr μ ν x ≤ c}, exp (- llr μ ν x) ∂μ := by
        refine setIntegral_mono_ae_restrict ?_ ?_ ?_
        · simp only [integrableOn_const]
          exact Or.inr ((measure_mono Set.inter_subset_left).trans_lt (Ne.lt_top hμs))
        · refine Integrable.integrableOn ?_
          refine (integrable_congr (exp_neg_llr hμν)).mpr ?_
          exact Measure.integrable_toReal_rnDeriv
        · rw [Filter.EventuallyLE, ae_restrict_iff]
          · refine ae_of_all _ (fun x hxs ↦ ?_)
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hxs
            simp [hxs.2]
          · exact (measurable_llr _ _).neg.exp measurableSet_Ici
  _ ≤ (ν (s ∩ {x | llr μ ν x ≤ c})).toReal := by
        refine setIntegral_exp_neg_llr_le hμν ?_
        exact ((measure_mono Set.inter_subset_left).trans_lt (measure_lt_top _ _)).ne
  _ ≤ (ν s).toReal := by
        rw [ENNReal.toReal_le_toReal _ (measure_ne_top _ _)]
        · exact measure_mono Set.inter_subset_left
        · exact ((measure_mono Set.inter_subset_left).trans_lt (measure_lt_top _ _)).ne

lemma measure_sub_le_measure_mul_exp' [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (s : Set α) (c : ℝ) (hμc : μ {x | c < llr μ ν x} ≠ ∞) :
    μ s - μ {x | c < llr μ ν x} ≤ (ν s) * ENNReal.ofReal (exp c) := by
  have h := measure_sub_le_measure_mul_exp hμν s c hμc
  by_cases h_le : μ {x | c < llr μ ν x} ≤ μ s
  · rw [← ENNReal.toReal_sub_of_le h_le (measure_ne_top _ _)] at h
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν s), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.le_ofReal_iff_toReal_le]
    · exact h
    · simp [measure_ne_top]
    · positivity
  · rw [tsub_eq_zero_of_le]
    · positivity
    · exact (not_le.mp h_le).le

lemma one_sub_le_add_measure_mul_exp [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    [IsProbabilityMeasure μ]
    (hμν : μ ≪ ν) (hμν' : μ ≪ ν') (s : Set α) (c c' : ℝ) :
    1 - (μ {x | c < llr μ ν x}).toReal - (μ {x | c' < llr μ ν' x}).toReal
      ≤ (ν s).toReal * exp c + (ν' sᶜ).toReal * exp c' := by
  have h := measure_sub_le_measure_mul_exp hμν s c (measure_ne_top _ _)
  have h' := measure_sub_le_measure_mul_exp hμν' sᶜ c' (measure_ne_top _ _)
  calc 1 - (μ {x | c < llr μ ν x}).toReal
      - (μ {x | c' < llr μ ν' x}).toReal
    ≤ (μ s).toReal + (μ sᶜ).toReal - (μ {x | c < llr μ ν x}).toReal
      - (μ {x | c' < llr μ ν' x}).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        gcongr
        rw [← ENNReal.one_toReal, ← measure_univ (μ := μ), ENNReal.toReal_le_toReal]
        · exact measure_univ_le_add_compl s
        · exact measure_ne_top _ _
        · simp only [ne_eq, ENNReal.add_eq_top, measure_ne_top μ, or_self, not_false_eq_true]
  _ = ((μ s).toReal - (μ {x | c < llr μ ν x}).toReal)
      + ((μ sᶜ).toReal - (μ {x | c' < llr μ ν' x}).toReal) := by abel
  _ ≤ (ν s).toReal * exp c + (ν' sᶜ).toReal * exp c' := by gcongr

lemma one_sub_le_add_measure_mul_exp' [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    [IsProbabilityMeasure μ] (hμν : μ ≪ ν) (hμν' : μ ≪ ν') (s : Set α) (c c' : ℝ) :
    1 - (μ {x | c < llr μ ν x}).toReal - (μ {x | c' < llr μ ν' x}).toReal
      ≤ ((ν s).toReal + (ν' sᶜ).toReal) * exp (max c c') := by
  refine (one_sub_le_add_measure_mul_exp hμν hμν' s c c').trans ?_
  rw [add_mul]
  gcongr
  · simp
  · exact le_max_right _ _

end ProbabilityTheory

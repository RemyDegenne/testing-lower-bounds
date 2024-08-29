/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.CurvatureMeasure
import TestingLowerBounds.StatInfoFun
import Mathlib.Order.CompletePartialOrder
import TestingLowerBounds.FDiv.Basic
import TestingLowerBounds.Testing.Binary
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import TestingLowerBounds.ForMathlib.SetIntegral

/-!
# Statistical information

## Main definitions

* `statInfo`

## Main statements

* `statInfo_comp_le`: data-processing inequality

## Notation

## Implementation details

-/

open MeasureTheory Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞} {π : Measure Bool} {f : ℝ → ℝ} {β γ x t : ℝ}

/-- The statistical information of the measures `μ` and `ν` with respect to
the prior `π ∈ ℳ({0,1})`. -/
noncomputable
def statInfo (μ ν : Measure 𝒳) (π : Measure Bool) : ℝ≥0∞ :=
  bayesBinaryRisk (Kernel.discard 𝒳 ∘ₘ μ) (Kernel.discard 𝒳 ∘ₘ ν) π - bayesBinaryRisk μ ν π

lemma statInfo_eq_min_sub (μ ν : Measure 𝒳) (π : Measure Bool) :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ) - bayesBinaryRisk μ ν π := by
  simp_rw [statInfo, Measure.comp_discard, bayesBinaryRisk_dirac]

lemma statInfo_eq_bayesRiskIncrease (μ ν : Measure 𝒳) (π : Measure Bool) :
    statInfo μ ν π
      = bayesRiskIncrease simpleBinaryHypTest (twoHypKernel μ ν) π (Kernel.discard 𝒳) := by
  simp_rw [statInfo, bayesBinaryRisk, bayesRiskIncrease, comp_twoHypKernel]

@[simp] lemma statInfo_zero_left : statInfo 0 ν π = 0 := by simp [statInfo]

@[simp] lemma statInfo_zero_right : statInfo μ 0 π = 0 := by simp [statInfo]

@[simp] lemma statInfo_zero_prior : statInfo μ ν 0 = 0 := by simp [statInfo]

@[simp] lemma statInfo_self : statInfo μ μ π = 0 := by simp [statInfo]

lemma statInfo_le_min : statInfo μ ν π ≤ min (π {false} * μ univ) (π {true} * ν univ) :=
  statInfo_eq_min_sub μ ν π ▸ tsub_le_self

lemma statInfo_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure π] :
    statInfo μ ν π ≠ ⊤ :=
  (statInfo_le_min.trans_lt <| min_lt_iff.mpr <| Or.inl
    <| ENNReal.mul_lt_top (measure_ne_top π _) (measure_ne_top μ _)).ne

lemma statInfo_symm : statInfo μ ν π = statInfo ν μ (π.map Bool.not) := by
  simp_rw [statInfo, bayesBinaryRisk_symm _ _ π]

lemma statInfo_of_measure_true_eq_zero (μ ν : Measure 𝒳) (hπ : π {true} = 0) :
    statInfo μ ν π = 0 :=
  le_antisymm (statInfo_le_min.trans (by simp [hπ])) zero_le'

lemma statInfo_of_measure_false_eq_zero (μ ν : Measure 𝒳) (hπ : π {false} = 0) :
    statInfo μ ν π = 0 :=
  le_antisymm (statInfo_le_min.trans (by simp [hπ])) zero_le'

/-- **Data processing inequality** for the statistical information. -/
lemma statInfo_comp_le (μ ν : Measure 𝒳) (π : Measure Bool) (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] :
    statInfo (η ∘ₘ μ) (η ∘ₘ ν) π ≤ statInfo μ ν π := by
  refine tsub_le_tsub ?_ (bayesBinaryRisk_le_bayesBinaryRisk_comp _ _ _ _)
  simp [Measure.bind_apply .univ (Kernel.measurable _)]

lemma toReal_statInfo_eq_toReal_sub [IsFiniteMeasure ν] [IsFiniteMeasure π] :
    (statInfo μ ν π).toReal = (min (π {false} * μ univ) (π {true} * ν univ)).toReal
      - (bayesBinaryRisk μ ν π).toReal := by
  rw [statInfo_eq_min_sub, ENNReal.toReal_sub_of_le]
  · exact bayesBinaryRisk_le_min _ _ _
  · simp only [ne_eq, min_eq_top, not_and]
    exact fun _ ↦  ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top ν _)

lemma statInfo_boolMeasure_le_statInfo {E : Set 𝒳} (hE : MeasurableSet E) :
    statInfo (Bool.boolMeasure (μ Eᶜ) (μ E)) (Bool.boolMeasure (ν Eᶜ) (ν E)) π
      ≤ statInfo μ ν π := by
  have h_meas : Measurable fun x ↦ Bool.ofNat (E.indicator 1 x) :=
    ((measurable_discrete _).comp' (measurable_one.indicator hE))
  let η : Kernel 𝒳 Bool := Kernel.deterministic (fun x ↦ Bool.ofNat (E.indicator 1 x)) h_meas
  have h_false : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {false} = Eᶜ := by
    ext x; simp [Bool.ofNat]
  have h_true : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {true} = E := by
    ext x; simp [Bool.ofNat]
  convert statInfo_comp_le μ ν π η <;>
  · ext
    · rw [Measure.comp_deterministic_eq_map, Measure.map_apply h_meas (by trivial), h_false,
        Bool.boolMeasure_apply_false]
    · rw [Measure.comp_deterministic_eq_map, Measure.map_apply h_meas (by trivial), h_true,
        Bool.boolMeasure_apply_true]

lemma statInfo_eq_min_sub_lintegral (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ∫⁻ x, min (π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x)
      (π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x) ∂(twoHypKernel μ ν ∘ₘ π) := by
  rw [statInfo_eq_min_sub, bayesBinaryRisk_eq_lintegral_min]

lemma statInfo_eq_min_sub_lintegral' {ζ : Measure 𝒳} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SigmaFinite ζ] (π : Measure Bool) [IsFiniteMeasure π] (hμζ : μ ≪ ζ) (hνζ : ν ≪ ζ) :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ∫⁻ x, min (π {false} * (∂μ/∂ζ) x) (π {true} * (∂ν/∂ζ) x) ∂ζ := by
  by_cases h_false : π {false} = 0
  · simp [statInfo, h_false, bayesBinaryRisk_of_measure_false_eq_zero]
  by_cases h_true : π {true} = 0
  · simp [statInfo, h_true, bayesBinaryRisk_of_measure_true_eq_zero]
  have hμac : μ ≪ (twoHypKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_measure_comp_twoHypKernel_left μ ν h_false
  have hνac : ν ≪ (twoHypKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_measure_comp_twoHypKernel_right μ ν h_true
  have hacζ : (twoHypKernel μ ν ∘ₘ π) ≪ ζ :=
    measure_comp_twoHypKernel _ _ _ ▸ (hνζ.smul _).add_left (hμζ.smul _)
  rw [statInfo_eq_min_sub_lintegral, ← lintegral_rnDeriv_mul hacζ (by fun_prop)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv hμac, Measure.rnDeriv_mul_rnDeriv hνac] with x hxμ hxν
  rw [ENNReal.mul_min, mul_comm, mul_comm _ (π _ * _), mul_assoc, mul_assoc]
  congr

lemma toReal_statInfo_eq_min_sub_integral (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    (statInfo μ ν π).toReal = min (π {false} * μ univ).toReal (π {true} * ν univ).toReal
      - ∫ x, min (π {false} * μ.rnDeriv (twoHypKernel μ ν ∘ₘ π) x).toReal
      (π {true} * ν.rnDeriv (twoHypKernel μ ν ∘ₘ π) x).toReal ∂(twoHypKernel μ ν ∘ₘ π) := by
  have hμ : π {false} * μ univ ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top μ _)
  have hν : π {true} * ν univ ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top ν _)
  rw [statInfo_eq_min_sub, ENNReal.toReal_sub_of_le (bayesBinaryRisk_le_min μ ν π)]
  swap; · simp only [ne_eq, min_eq_top, hμ, hν, and_self, not_false_eq_true]
  rw [toReal_bayesBinaryRisk_eq_integral_min,
    MonotoneOn.map_min (fun _ _ _ hb hab ↦ ENNReal.toReal_mono hb hab) hμ hν]

lemma toReal_statInfo_eq_min_sub_integral' {ζ : Measure 𝒳} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SigmaFinite ζ] (π : Measure Bool) [IsFiniteMeasure π]  (hμζ : μ ≪ ζ) (hνζ : ν ≪ ζ) :
    (statInfo μ ν π).toReal = min (π {false} * μ univ).toReal (π {true} * ν univ).toReal
      - ∫ x, min (π {false} * (∂μ/∂ζ) x).toReal (π {true} * (∂ν/∂ζ) x).toReal ∂ζ := by
  have hμ : π {false} * μ univ ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top μ _)
  have hν : π {true} * ν univ ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top ν _)
  rw [statInfo_eq_min_sub_lintegral' π hμζ hνζ, ENNReal.toReal_sub_of_le]
  rotate_left
  · sorry
  · simp only [ne_eq, min_eq_top, hμ, hν, and_self, not_false_eq_true]
  rw [MonotoneOn.map_min (fun _ _ _ hb hab ↦ ENNReal.toReal_mono hb hab) hμ hν]
  sorry

lemma statInfo_eq_abs_add_lintegral_abs (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    statInfo μ ν π = 2⁻¹ * (∫⁻ x, ‖(π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal
      - (π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal‖₊ ∂(twoHypKernel μ ν ∘ₘ π)
      - (↑|(π {false} * μ univ).toReal - (π {true} * ν univ).toReal| : EReal)) := by
  have hμ : π {false} * μ univ ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top μ _)
  have hν : π {true} * ν univ ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top ν _)
  rw [statInfo_eq_min_sub, bayesBinaryRisk_eq_lintegral_ennnorm]
  rw [← ENNReal.ofReal_toReal (a := min _ _)]
  swap
  · simp only [ne_eq, min_eq_top, hμ, hν, and_self, not_false_eq_true]
  rw [MonotoneOn.map_min (fun _ _ _ hb hab ↦ ENNReal.toReal_mono hb hab) hμ hν]
  rw [min_eq_add_sub_abs_sub]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sub _ (abs_nonneg _)]
  rw [ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  rw [ENNReal.ofReal_toReal hμ, ENNReal.ofReal_toReal hν]
  simp_rw [ENNReal.mul_sub (fun _ _ ↦ ENNReal.inv_ne_top.mpr (NeZero.ne 2))]
  nth_rw 1 [measure_comp_twoHypKernel]
  simp_rw [Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply, smul_eq_mul, add_comm]
  --this is hard to prove, because we have to deal with a lot of ENNReals and subtractions and they do not work well together, for now I am leaving this. Maybe it could be a good idea to do the toReal version first, proving it starting from the previous lemma (making a toReal version of that as well) essentially mimiking the results for the binary, but here we would have to do double the work, because we have both the version with twoHypKernel μ ν ∘ₘ π and the one with ζ
  sorry

lemma toReal_statInfo_eq_integral_max_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure π] (h : π {false} * μ univ ≤ π {true} * ν univ) :
    (statInfo μ ν π).toReal
      = ∫ x, max 0 ((π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal) ∂ν
        + (π {false} * μ.singularPart ν univ).toReal := by
  by_cases h_false : π {false} = 0
  · simp [statInfo, h_false, bayesBinaryRisk_of_measure_false_eq_zero]
  by_cases h_true : π {true} = 0
  · simp [statInfo, h_true, bayesBinaryRisk_of_measure_true_eq_zero] at h ⊢
    rcases h with (h | h)
    · simp [h]
    · rw [integral_congr_ae (g := 0)]
      swap
      · filter_upwards [ν.rnDeriv_zero] with x hx
        simp [h, hx]
      simp [h]
  have hμac : μ ≪ (twoHypKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_measure_comp_twoHypKernel_left μ ν h_false
  have hνac : ν ≪ (twoHypKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_measure_comp_twoHypKernel_right μ ν h_true
  rw [toReal_statInfo_eq_min_sub_integral, min_eq_left ((ENNReal.toReal_le_toReal _ _).mpr h)]
    <;> try simp only [ne_eq, measure_ne_top _ _, not_false_eq_true, ENNReal.mul_ne_top]
  let s := μ.singularPartSet ν
  have hs : MeasurableSet s := Measure.measurableSet_singularPartSet
  calc
    _ = (π {false} * μ univ).toReal
        - ∫ x, (π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal
          + min 0 ((π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal
            - (π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal) ∂twoHypKernel μ ν ∘ₘ π := by
      congr with x
      nth_rw 1 [← add_zero (π _ * _).toReal, ← add_sub_cancel_left
        (π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal (π {true} * _).toReal]
      rw [add_sub_assoc, min_add_add_left]
    _ = (π {false} * μ univ).toReal
        - (∫ x, (π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal ∂twoHypKernel μ ν ∘ₘ π
        + ∫ x, min 0 ((π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal
            - (π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal) ∂twoHypKernel μ ν ∘ₘ π) := by
      simp_rw [ENNReal.toReal_mul, ← inf_eq_min]
      congr
      refine integral_add (Integrable.const_mul Measure.integrable_toReal_rnDeriv _) ?_
      refine (integrable_zero _ _ _).inf (Integrable.sub ?_ ?_) <;>
      · exact Measure.integrable_toReal_rnDeriv.const_mul _
    _ = - ∫ x, min 0 ((π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal
          - (π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal) ∂twoHypKernel μ ν ∘ₘ π := by
      simp_rw [ENNReal.toReal_mul, ← sub_sub, sub_eq_neg_self, sub_eq_zero, integral_mul_left,
        Measure.integral_toReal_rnDeriv hμac]
    _ = ∫ x, max 0 ((π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal
        - (π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal) ∂twoHypKernel μ ν ∘ₘ π := by
      simp [← integral_neg, ← inf_eq_min, ← sup_eq_max, neg_inf]
    _ = ∫ x in s, max 0 ((π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal
          - (π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal) ∂twoHypKernel μ ν ∘ₘ π
        + ∫ x in sᶜ, max 0 ((π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal
          - (π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal) ∂twoHypKernel μ ν ∘ₘ π := by
      simp_rw [ENNReal.toReal_mul]
      refine integral_add_compl hs ((integrable_zero _ _ _).sup (Integrable.sub ?_ ?_)) |>.symm <;>
      · exact Measure.integrable_toReal_rnDeriv.const_mul _
    _ = ∫ x in s, max 0 (π {false} * (∂(μ.singularPart ν)/∂twoHypKernel μ ν ∘ₘ π) x).toReal
          ∂twoHypKernel μ ν ∘ₘ π
        + ∫ x in sᶜ, (max 0
            ((π {false} * (∂μ.restrict (μ.singularPartSet ν)ᶜ/∂ν) x).toReal - (π {true}).toReal))
          * ((∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal ∂twoHypKernel μ ν ∘ₘ π := by
      congr 1
      · apply setIntegral_congr_ae hs
        filter_upwards [μ.rnDeriv_eq_zero_ae_of_singularPartSet ν _,
          (μ.singularPart ν).rnDeriv_add' (ν.withDensity (μ.rnDeriv ν)) (twoHypKernel μ ν ∘ₘ π),
          Measure.rnDeriv_withDensity_left_of_absolutelyContinuous hνac
          (μ.measurable_rnDeriv ν).aemeasurable] with x hx1 hx2 hx3
        intro hxs
        nth_rw 1 [← μ.singularPart_add_rnDeriv ν]
        simp_rw [hx2, Pi.add_apply, hx3, hx1 hxs, mul_zero, ENNReal.zero_toReal, sub_zero, add_zero]
      · apply setIntegral_congr_ae hs.compl
        filter_upwards [μ.rnDeriv_restrict (twoHypKernel μ ν ∘ₘ π) hs.compl,
          Measure.rnDeriv_mul_rnDeriv
          (μ.absolutelyContinuous_restrict_compl_singularPartSet ν)] with x hx1 hx2 hxs
        rw [max_mul_of_nonneg _ _ ENNReal.toReal_nonneg, zero_mul, sub_mul]
        rw [Set.indicator_of_mem hxs] at hx1
        simp_rw [ENNReal.toReal_mul, mul_assoc, ← hx1, ← hx2, Pi.mul_apply, ENNReal.toReal_mul]
    _ = ∫ x, max 0 (π {false} * (∂(μ.singularPart ν)/∂twoHypKernel μ ν ∘ₘ π) x).toReal
          ∂twoHypKernel μ ν ∘ₘ π
        + ∫ x in sᶜ, (max 0 ((π {false}
          * (∂μ.restrict (μ.singularPartSet ν)ᶜ/∂ν) x).toReal - (π {true}).toReal)) ∂ν := by
      congr 1
      · nth_rw 2 [← integral_add_compl hs]
        swap
        · simp_rw [ENNReal.toReal_mul]
          exact ((integrable_zero _ _ _).sup (Measure.integrable_toReal_rnDeriv.const_mul _))
        refine self_eq_add_right.mpr <| setIntegral_eq_zero_of_ae_eq_zero ?_
        filter_upwards [μ.rnDeriv_restrict _ hs] with x hx
        intro hxs
        rw [← Measure.restrict_singularPartSet_eq_singularPart, hx, indicator_of_not_mem hxs,
          mul_zero, ENNReal.zero_toReal, max_self]
      · simp_rw [mul_comm _ ((∂ν/∂_ ∘ₘ _) _).toReal, ← smul_eq_mul]
        rw [setIntegral_rnDeriv_smul hνac hs.compl]
    _ = ∫ x, (π {false} * (∂(μ.singularPart ν)/∂twoHypKernel μ ν ∘ₘ π) x).toReal
          ∂twoHypKernel μ ν ∘ₘ π
        + ∫ x in sᶜ, (max 0 ((π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal)) ∂ν := by
      simp_rw [max_eq_right ENNReal.toReal_nonneg]
      congr 1
      apply setIntegral_congr_ae hs.compl
      filter_upwards [μ.rnDeriv_restrict ν hs.compl] with x hx1 hxs
      rw [hx1, indicator_of_mem hxs]
    _ = ∫ x, (max 0 ((π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal)) ∂ν
        + (π {false} * (μ.singularPart ν) univ).toReal := by
      simp_rw [ENNReal.toReal_mul, add_comm (∫ _, _ ∂_ ∘ₘ _)]
      rw [integral_mul_left, Measure.integral_toReal_rnDeriv
        ((μ.singularPart_le ν).absolutelyContinuous.trans hμac)]
      nth_rw 2 [← integral_add_compl hs]
      swap
      · exact (integrable_zero _ _ _).sup
          ((Measure.integrable_toReal_rnDeriv.const_mul _).sub (integrable_const _))
      rw [setIntegral_zero_measure _ (μ.measure_singularPartSet ν), zero_add]

/- TODO: Try to prove `toReal_statInfo_eq_integral_max_of_gt` using the previous lemma and the
symmetry of the statInfo. This should be faster than the current proof, and avoid a lot of code
duplication. To finish the proof we would need something like `∂μ/∂ν * ∂ν/∂μ =ᵐ[μ] 1`, at least
when `∂ν/∂μ ≠ 0`, and also that `∂μ/∂ν =ᵐ[ν.simgularPart μ] 0`, if we have this we can split `ν`
using the Lebesgue decomposition and we should be done quite easily.
-/
-- lemma toReal_statInfo_eq_integral_max_of_gt' {μ ν : Measure 𝒳} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     {π : Measure Bool} [IsFiniteMeasure π] (h : π {true} * ν univ < π {false} * μ univ) :
--     (statInfo μ ν π).toReal
--       = ∫ x, max 0 ((π {true}).toReal - (π {false} * (∂μ/∂ν) x).toReal) ∂ν := by
--   have h1 : (Measure.map Bool.not π) {false} = π {true} := by sorry
--   have h2 : (Measure.map Bool.not π) {true} = π {false} := by sorry
--   rw [statInfo_symm]
--   rw [toReal_statInfo_eq_integral_max_of_le]
--   swap
--   · rw [h1, h2]
--     exact h.le
--   rw [h1, h2]
--   sorry

lemma toReal_statInfo_eq_integral_max_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure π] (h : π {true} * ν univ < π {false} * μ univ) :
    (statInfo μ ν π).toReal
      = ∫ x, max 0 ((π {true}).toReal - (π {false} * (∂μ/∂ν) x).toReal) ∂ν := by
  by_cases h_false : π {false} = 0
  · simp [h_false] at h
  by_cases h_true : π {true} = 0
  · have (x : 𝒳) : 0 ≥ -((π {false}).toReal * ((∂μ/∂ν) x).toReal) := neg_nonpos.mpr (by positivity)
    simp [statInfo, h_true, bayesBinaryRisk_of_measure_true_eq_zero, max_eq_left (this _)]
  have hνac : ν ≪ (twoHypKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_measure_comp_twoHypKernel_right μ ν h_true
  rw [toReal_statInfo_eq_min_sub_integral, min_eq_right ((ENNReal.toReal_le_toReal _ _).mpr h.le)]
    <;> try simp only [ne_eq, measure_ne_top _ _, not_false_eq_true, ENNReal.mul_ne_top]
  let s := μ.singularPartSet ν
  have hs : MeasurableSet s := Measure.measurableSet_singularPartSet
  calc
    _ = (π {true} * ν univ).toReal
        - ∫ x, (π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal
          + min 0 ((π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal
            - (π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal) ∂twoHypKernel μ ν ∘ₘ π := by
      congr with x
      nth_rw 1 [min_comm, ← add_zero (π _ * _).toReal, ← add_sub_cancel_left
        (π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal (π {false} * _).toReal]
      rw [add_sub_assoc, min_add_add_left]
    _ = (π {true} * ν univ).toReal
        - (∫ x, (π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal ∂twoHypKernel μ ν ∘ₘ π
        + ∫ x, min 0 ((π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal
            - (π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal) ∂twoHypKernel μ ν ∘ₘ π) := by
      simp_rw [ENNReal.toReal_mul, ← inf_eq_min]
      congr
      refine integral_add (Integrable.const_mul Measure.integrable_toReal_rnDeriv _) ?_
      refine (integrable_zero _ _ _).inf (Integrable.sub ?_ ?_) <;>
      · exact Measure.integrable_toReal_rnDeriv.const_mul _
    _ = - ∫ x, min 0 ((π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal
          - (π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal) ∂twoHypKernel μ ν ∘ₘ π := by
      simp_rw [ENNReal.toReal_mul, ← sub_sub, sub_eq_neg_self, sub_eq_zero, integral_mul_left,
        Measure.integral_toReal_rnDeriv hνac]
    _ = ∫ x, max 0 ((π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal
        - (π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal) ∂twoHypKernel μ ν ∘ₘ π := by
      simp [← integral_neg, ← inf_eq_min, ← sup_eq_max, neg_inf]
    _ = ∫ x in s, max 0 ((π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal
          - (π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal) ∂twoHypKernel μ ν ∘ₘ π
        + ∫ x in sᶜ, max 0 ((π {true} * (∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal
          - (π {false} * (∂μ/∂twoHypKernel μ ν ∘ₘ π) x).toReal) ∂twoHypKernel μ ν ∘ₘ π := by
      simp_rw [ENNReal.toReal_mul]
      refine integral_add_compl hs ((integrable_zero _ _ _).sup (Integrable.sub ?_ ?_)) |>.symm <;>
      · exact Measure.integrable_toReal_rnDeriv.const_mul _
    _ = ∫ x in s, max 0 (-(π {false} * (∂(μ.singularPart ν)/∂twoHypKernel μ ν ∘ₘ π) x).toReal)
          ∂twoHypKernel μ ν ∘ₘ π
        + ∫ x in sᶜ, (max 0
            ((π {true}).toReal - (π {false} * (∂μ.restrict (μ.singularPartSet ν)ᶜ/∂ν) x).toReal))
          * ((∂ν/∂twoHypKernel μ ν ∘ₘ π) x).toReal ∂twoHypKernel μ ν ∘ₘ π := by
      congr 1
      · apply setIntegral_congr_ae hs
        filter_upwards [μ.rnDeriv_eq_zero_ae_of_singularPartSet ν _,
          (μ.singularPart ν).rnDeriv_add' (ν.withDensity (μ.rnDeriv ν)) (twoHypKernel μ ν ∘ₘ π),
          Measure.rnDeriv_withDensity_left_of_absolutelyContinuous hνac
          (μ.measurable_rnDeriv ν).aemeasurable] with x hx1 hx2 hx3 hxs
        nth_rw 2 [← μ.singularPart_add_rnDeriv ν]
        simp_rw [hx2, Pi.add_apply, hx3, hx1 hxs, mul_zero, ENNReal.zero_toReal, zero_sub, add_zero]
      · apply setIntegral_congr_ae hs.compl
        filter_upwards [μ.rnDeriv_restrict (twoHypKernel μ ν ∘ₘ π) hs.compl,
          Measure.rnDeriv_mul_rnDeriv
          (μ.absolutelyContinuous_restrict_compl_singularPartSet ν)] with x hx1 hx2 hxs
        rw [max_mul_of_nonneg _ _ ENNReal.toReal_nonneg, zero_mul, sub_mul]
        rw [Set.indicator_of_mem hxs] at hx1
        simp_rw [ENNReal.toReal_mul, mul_assoc, ← hx1, ← hx2, Pi.mul_apply, ENNReal.toReal_mul]
    _ = ∫ x in sᶜ, max 0 ((π {true}).toReal
          - (π {false} * (∂μ.restrict (μ.singularPartSet ν)ᶜ/∂ν) x).toReal) ∂ν := by
      simp_rw [max_eq_left (neg_nonpos.mpr ENNReal.toReal_nonneg),
        mul_comm _ ((∂ν/∂_ ∘ₘ _) _).toReal, ← smul_eq_mul, setIntegral_rnDeriv_smul hνac hs.compl]
      simp
    _ = ∫ x in sᶜ, (max 0 ((π {true}).toReal - (π {false} * (∂μ/∂ν) x).toReal)) ∂ν := by
      apply setIntegral_congr_ae hs.compl
      filter_upwards [μ.rnDeriv_restrict ν hs.compl] with x hx1 hxs
      rw [hx1, indicator_of_mem hxs]
    _ = ∫ x, (max 0 ((π {true}).toReal - (π {false} * (∂μ/∂ν) x).toReal)) ∂ν := by
      simp_rw [ENNReal.toReal_mul]
      nth_rw 2 [← integral_add_compl hs]
      swap
      · exact (integrable_zero _ _ _).sup
          ((integrable_const _).sub (Measure.integrable_toReal_rnDeriv.const_mul _))
      rw [setIntegral_zero_measure _ (μ.measure_singularPartSet ν), zero_add]

lemma statInfo_eq_lintegral_max_of_le (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] (h : π {false} * μ univ ≤ π {true} * ν univ) :
    statInfo μ ν π
      = ∫⁻ x, max 0 (π {false} * (∂μ/∂ν) x - π {true}) ∂ν + π {false} * μ.singularPart ν univ := by
  sorry

lemma statInfo_eq_lintegral_max_of_gt (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] (h : π {true} * ν univ < π {false} * μ univ) :
    statInfo μ ν π = ∫⁻ x, max 0 (π {true} - π {false} * (∂μ/∂ν) x) ∂ν := by
  sorry

lemma toReal_statInfo_eq_integral_abs (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {π : Measure Bool} [IsFiniteMeasure π]  :
    (statInfo μ ν π).toReal
      = 2⁻¹ * (-|(π {false} * μ univ).toReal - (π {true} * ν univ).toReal|
        + ∫ x, |(π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal| ∂ν
        + (π {false} * (μ.singularPart ν) univ).toReal) := by
  rcases le_or_lt (π {false} * μ univ) (π {true} * ν univ) with (h | h)
  · rw [abs_of_nonpos]
    swap
    · refine sub_nonpos.mpr <| (ENNReal.toReal_le_toReal ?_ ?_).mpr h
        <;> try simp only [ne_eq, measure_ne_top _ _, not_false_eq_true, ENNReal.mul_ne_top]
    simp_rw [toReal_statInfo_eq_integral_max_of_le h, max_eq_add_add_abs_sub, zero_add, zero_sub,
      integral_mul_left, abs_neg, neg_sub]
    calc
      _ = 2⁻¹ * (∫ x, (π {false} * (∂μ/∂ν) x).toReal ∂ν - ∫ _, (π {true}).toReal ∂ν
            + ∫ x, |(π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal| ∂ν)
          + (π {false} * (μ.singularPart ν) univ).toReal := by
        simp_rw [ENNReal.toReal_mul]
        have : Integrable (fun x ↦ (π {false}).toReal * ((∂μ/∂ν) x).toReal - (π {true}).toReal) ν :=
          (Measure.integrable_toReal_rnDeriv.const_mul _).sub (integrable_const _)
        rw [integral_add this this.abs, integral_sub
          (Measure.integrable_toReal_rnDeriv.const_mul _) (integrable_const _)]
      _ = 2⁻¹ * ((π {false} * μ univ).toReal - (π {false} * (μ.singularPart ν) univ).toReal
            - (π {true} * ν univ).toReal
            + ∫ x, |(π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal| ∂ν)
          + (π {false} * (μ.singularPart ν) univ).toReal := by
        congr
        · simp_rw [ENNReal.toReal_mul, integral_mul_left, Measure.integral_toReal_rnDeriv', mul_sub]
        · rw [integral_const, smul_eq_mul, ENNReal.toReal_mul, mul_comm]
      _ = _ := by ring
  · rw [abs_of_nonneg]
    swap
    · refine sub_nonneg.mpr <| (ENNReal.toReal_le_toReal ?_ ?_).mpr h.le
        <;> try simp only [ne_eq, measure_ne_top _ _, not_false_eq_true, ENNReal.mul_ne_top]
    simp_rw [toReal_statInfo_eq_integral_max_of_gt h, max_eq_add_add_abs_sub, zero_add, zero_sub,
      integral_mul_left, abs_neg, neg_sub]
    calc
      _ = 2⁻¹ * (∫ _, (π {true}).toReal ∂ν - ∫ x, (π {false} * (∂μ/∂ν) x).toReal ∂ν
            + ∫ x, |(π {true}).toReal - (π {false} * (∂μ/∂ν) x).toReal| ∂ν) := by
        simp_rw [ENNReal.toReal_mul]
        have : Integrable (fun x ↦ (π {true}).toReal - (π {false}).toReal * ((∂μ/∂ν) x).toReal) ν :=
          (integrable_const _).sub (Measure.integrable_toReal_rnDeriv.const_mul _)
        rw [integral_add this this.abs, integral_sub (integrable_const _)
          (Measure.integrable_toReal_rnDeriv.const_mul _)]
      _ = 2⁻¹ * ((π {true} * ν univ).toReal - (π {false} * μ univ).toReal
            + (π {false} * (μ.singularPart ν) univ).toReal
            + ∫ x, |(π {true}).toReal - (π {false} * (∂μ/∂ν) x).toReal| ∂ν) := by
        simp_rw [ENNReal.toReal_mul, integral_mul_left, Measure.integral_toReal_rnDeriv', mul_sub]
        rw [integral_const, smul_eq_mul, ← sub_add, mul_comm (ν univ).toReal]
      _ = _ := by
        simp_rw [abs_sub_comm]
        ring

lemma statInfo_eq_min_sub_iInf_measurableSet (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ⨅ E, ⨅ (_ : MeasurableSet E), π {false} * μ E + π {true} * ν Eᶜ := by
  rw [statInfo_eq_min_sub, bayesBinaryRisk_eq_iInf_measurableSet]

section StatInfoFun

open Set Filter ConvexOn

lemma integrable_statInfoFun_rnDeriv (β γ : ℝ)
    (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x ↦ statInfoFun β γ ((∂μ/∂ν) x).toReal) ν := by
  refine integrable_f_rnDeriv_of_derivAtTop_ne_top _ _ stronglyMeasurable_statInfoFun3
    ?_ (derivAtTop_statInfoFun_ne_top β γ)
  exact (convexOn_statInfoFun β γ).subset (fun _ _ ↦ trivial) (convex_Ici 0)

lemma nnReal_mul_fDiv {a : NNReal} :
    a * fDiv (statInfoFun β γ) μ ν = fDiv (fun x ↦ statInfoFun (a * β) (a * γ) x) μ ν := by
  change (a.1 : EReal) * _ = _
  rw [← fDiv_mul a.2 ((convexOn_statInfoFun β γ).subset (fun _ _ ↦ trivial) (convex_Ici 0)) μ ν]
  simp_rw [const_mul_statInfoFun a.2]
  rfl

lemma fDiv_statInfoFun_nonneg : 0 ≤ fDiv (statInfoFun β γ) μ ν :=
  fDiv_nonneg_of_nonneg (fun x ↦ statInfoFun_nonneg β γ x) (derivAtTop_statInfoFun_nonneg β γ)

lemma fDiv_statInfoFun_stronglyMeasurable (μ ν : Measure 𝒳) [SFinite ν] :
    StronglyMeasurable (Function.uncurry fun β γ ↦ fDiv (statInfoFun β γ) μ ν) := by
  simp_rw [fDiv]
  have h_meas := stronglyMeasurable_statInfoFun.measurable.comp
    (f := fun ((a, b), x) ↦ ((a, b), ((∂μ/∂ν) x).toReal)) (measurable_fst.prod_mk (by fun_prop))
    |>.stronglyMeasurable
  refine Measurable.ite ?_ measurable_const ?_ |>.stronglyMeasurable
  · rw [← Set.compl_setOf, MeasurableSet.compl_iff]
    exact measurableSet_integrable h_meas
  · refine StronglyMeasurable.integral_prod_right (by exact h_meas)
      |>.measurable.coe_real_ereal.add ?_
    simp_rw [derivAtTop_statInfoFun_eq]
    refine (Measurable.coe_real_ereal ?_).mul_const _
    apply Measurable.ite (measurableSet_le measurable_const measurable_fst)
      <;> refine Measurable.ite (measurableSet_le measurable_snd measurable_fst) ?_ ?_ <;> fun_prop

lemma fDiv_statInfoFun_eq_integral_max_of_nonneg_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν = ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν := by
  simp_rw [fDiv_of_integrable (integrable_statInfoFun_rnDeriv _ _ _ _),
    derivAtTop_statInfoFun_of_nonneg_of_le hβ hγ, zero_mul, add_zero, statInfoFun_of_le hγ]

lemma fDiv_statInfoFun_eq_integral_max_of_nonneg_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : β < γ) :
    fDiv (statInfoFun β γ) μ ν
      = ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν + β * (μ.singularPart ν) univ := by
  simp_rw [fDiv_of_integrable (integrable_statInfoFun_rnDeriv _ _ _ _),
    derivAtTop_statInfoFun_of_nonneg_of_gt hβ hγ, statInfoFun_of_gt hγ]

lemma fDiv_statInfoFun_eq_integral_max_of_nonpos_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν
      = ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν - β * (μ.singularPart ν) univ := by
  simp_rw [fDiv_of_integrable (integrable_statInfoFun_rnDeriv _ _ _ _),
    derivAtTop_statInfoFun_of_nonpos_of_le hβ hγ, statInfoFun_of_le hγ, neg_mul, ← sub_eq_add_neg]

lemma fDiv_statInfoFun_eq_integral_max_of_nonpos_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : β < γ) :
    fDiv (statInfoFun β γ) μ ν = ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν := by
  simp_rw [fDiv_of_integrable (integrable_statInfoFun_rnDeriv _ _ _ _),
    derivAtTop_statInfoFun_of_nonpos_of_gt hβ hγ, statInfoFun_of_gt hγ, zero_mul, add_zero]

lemma fDiv_statInfoFun_eq_zero_of_nonneg_of_nonpos [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : γ ≤ 0) :
    fDiv (statInfoFun β γ) μ ν = 0 := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonneg_of_le hβ (hγ.trans hβ), EReal.coe_eq_zero]
  convert integral_zero 𝒳 ℝ with x
  exact max_eq_left <| tsub_nonpos.mpr <| hγ.trans <| mul_nonneg hβ ENNReal.toReal_nonneg

lemma fDiv_statInfoFun_eq_zero_of_nonpos_of_pos [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : 0 < γ) :
    fDiv (statInfoFun β γ) μ ν = 0 := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonpos_of_gt hβ (hβ.trans_lt hγ), EReal.coe_eq_zero]
  convert integral_zero 𝒳 ℝ with x
  exact max_eq_left <| tsub_nonpos.mpr <|
    (mul_nonpos_iff.mpr <| Or.inr ⟨hβ, ENNReal.toReal_nonneg⟩).trans hγ.le

/-- Auxiliary lemma for `fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_le` and
`fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_le`. -/
lemma integral_max_eq_integral_abs [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν
      = 2⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν + γ * (ν univ).toReal - β * (μ univ).toReal
        + β * ((μ.singularPart ν) univ).toReal) := by
  simp_rw [max_eq_add_add_abs_sub, zero_add, zero_sub, neg_sub, integral_mul_left]
  congr
  have h_int : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have h_int' : Integrable (fun x ↦ γ - β * ((∂μ/∂ν) x).toReal) ν := (integrable_const γ).sub h_int
  rw [integral_add h_int', integral_sub (integrable_const γ) h_int, integral_const, smul_eq_mul,
    mul_comm, integral_mul_left, add_comm, add_sub_assoc, add_assoc, sub_eq_add_neg, sub_eq_add_neg,
    add_assoc, ← mul_neg, ← mul_neg, ← mul_add]
  swap; · exact (integrable_add_const_iff.mpr h_int).abs
  congr
  nth_rw 2 [μ.haveLebesgueDecomposition_add ν]
  simp only [Measure.coe_add, Pi.add_apply, MeasurableSet.univ, withDensity_apply,
    Measure.restrict_univ]
  rw [ENNReal.toReal_add (measure_ne_top _ _)]
  swap; · exact lt_top_iff_ne_top.mp <| (setLIntegral_univ _ ▸
    Measure.setLIntegral_rnDeriv_le univ).trans_lt IsFiniteMeasure.measure_univ_lt_top
  ring_nf
  rw [integral_toReal (μ.measurable_rnDeriv ν).aemeasurable (μ.rnDeriv_lt_top ν)]

/-- Auxiliary lemma for `fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_gt` and
`fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_gt`. -/
lemma integral_max_eq_integral_abs' [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν
      = 2⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν - γ * (ν univ).toReal + β * (μ univ).toReal
        - β * ((μ.singularPart ν) univ).toReal) := by
  simp_rw [max_eq_add_add_abs_sub, zero_add, zero_sub, abs_neg, integral_mul_left]
  congr
  have h_int : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have h_int' : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal - γ) ν := h_int.sub (integrable_const γ)
  rw [integral_add h_int', integral_sub h_int (integrable_const γ), integral_const, smul_eq_mul,
    mul_comm, integral_mul_left, add_comm, add_sub_assoc, sub_eq_add_neg, add_comm (β * _),
    ← add_assoc, ← sub_eq_add_neg]
  swap; · exact (h_int.sub (integrable_const _)).abs
  congr
  nth_rw 2 [μ.haveLebesgueDecomposition_add ν]
  simp only [Measure.coe_add, Pi.add_apply, MeasurableSet.univ, withDensity_apply,
    Measure.restrict_univ]
  rw [ENNReal.toReal_add (measure_ne_top _ _)]
  swap; · exact lt_top_iff_ne_top.mp <| (setLIntegral_univ _ ▸
    Measure.setLIntegral_rnDeriv_le univ).trans_lt IsFiniteMeasure.measure_univ_lt_top
  ring_nf
  rw [integral_toReal (μ.measurable_rnDeriv ν).aemeasurable (μ.rnDeriv_lt_top ν)]

lemma fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      + β * (μ.singularPart ν) univ + γ * ν univ - β * μ univ) := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonneg_of_le hβ hγ, integral_max_eq_integral_abs,
    sub_eq_add_neg, add_assoc, add_comm (- _), ← add_assoc, ← sub_eq_add_neg, add_assoc,
    add_comm (_ * _), add_assoc]
  simp only [EReal.coe_mul, EReal.coe_sub, EReal.coe_add,
    EReal.coe_ennreal_toReal (measure_ne_top _ _)]

lemma fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : β < γ) :
    fDiv (statInfoFun β γ) μ ν = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      + β * (μ.singularPart ν) univ + β * μ univ - γ * ν univ) := by
  have h_eq :
      (β : EReal) * ((μ.singularPart ν) univ)
        = ↑(2⁻¹ * (2 * β * ((μ.singularPart ν) univ).toReal)) := by
    simp [mul_assoc, EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  rw [fDiv_statInfoFun_eq_integral_max_of_nonneg_of_gt hβ hγ, integral_max_eq_integral_abs', h_eq,
    ← EReal.coe_add, ← mul_add, EReal.coe_mul]
  simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, sub_eq_add_neg,
    ← EReal.coe_neg, ← EReal.coe_add, add_assoc]
  congr 3
  ring

lemma fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      - β * (μ.singularPart ν) univ + γ * ν univ - β * μ univ) := by
  have h_eq :
      (β : EReal) * ((μ.singularPart ν) univ)
        = ↑(2⁻¹ * (2 * β * ((μ.singularPart ν) univ).toReal)) := by
    simp [mul_assoc, EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  rw [fDiv_statInfoFun_eq_integral_max_of_nonpos_of_le hβ hγ, integral_max_eq_integral_abs, h_eq,
    sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_add, ← mul_neg, ← mul_add, EReal.coe_mul]
  simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, sub_eq_add_neg,
    ← EReal.coe_neg, ← EReal.coe_add, add_assoc]
  congr 3
  ring

lemma fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : β < γ) :
    fDiv (statInfoFun β γ) μ ν = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      - β * (μ.singularPart ν) univ + β * μ univ - γ * ν univ) := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonpos_of_gt hβ hγ, integral_max_eq_integral_abs']
  simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, sub_eq_add_neg,
    ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_mul]
  ring_nf

lemma fDiv_statInfoFun_eq_StatInfo_of_nonneg_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hγβ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν = statInfo μ ν (Bool.boolMeasure (.ofReal β) (.ofReal γ))
      + 2⁻¹ * (|β * (μ univ).toReal - γ * (ν univ).toReal|
        + γ * (ν univ).toReal - β * (μ univ).toReal) := by
  rw [← ENNReal.toReal_toEReal_of_ne_top statInfo_ne_top, toReal_statInfo_eq_integral_abs]
  simp only [Bool.boolMeasure_apply_false, ENNReal.toReal_mul, hβ, ENNReal.toReal_ofReal,
    Bool.boolMeasure_apply_true, hγ, EReal.coe_mul, EReal.coe_add, EReal.coe_neg,
    ENNReal.toReal_toEReal_of_ne_top (measure_ne_top _ _)]
  rw [show 2⁻¹ = ((2⁻¹ : ℝ) : EReal) from rfl, ← EReal.coe_mul_add_of_nonneg (by positivity),
    fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_le hβ hγβ]
  simp_rw [sub_eq_add_neg, ← add_assoc]
  rw [add_comm (-_ + _ + _)]
  simp_rw [← add_assoc, ← sub_eq_add_neg, ]
  rw [EReal.sub_self (EReal.coe_ne_top _) (EReal.coe_ne_bot _), zero_add]

lemma fDiv_statInfoFun_eq_StatInfo_of_nonneg_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hγβ : β < γ) :
    fDiv (statInfoFun β γ) μ ν = statInfo μ ν (Bool.boolMeasure (.ofReal β) (.ofReal γ))
      + 2⁻¹ * (|β * (μ univ).toReal - γ * (ν univ).toReal|
        + β * (μ univ).toReal - γ * (ν univ).toReal) := by
  rw [← ENNReal.toReal_toEReal_of_ne_top statInfo_ne_top, toReal_statInfo_eq_integral_abs]
  simp only [Bool.boolMeasure_apply_false, ENNReal.toReal_mul, hβ, ENNReal.toReal_ofReal,
    Bool.boolMeasure_apply_true, hγ, EReal.coe_mul, EReal.coe_add, EReal.coe_neg,
    ENNReal.toReal_toEReal_of_ne_top (measure_ne_top _ _)]
  rw [show 2⁻¹ = ((2⁻¹ : ℝ) : EReal) from rfl, ← EReal.coe_mul_add_of_nonneg (by positivity),
    fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_gt hβ hγβ]
  simp_rw [sub_eq_add_neg, ← add_assoc]
  rw [add_comm (-_ + _ + _)]
  simp_rw [← add_assoc, ← sub_eq_add_neg, ]
  rw [EReal.sub_self (EReal.coe_ne_top _) (EReal.coe_ne_bot _), zero_add]

-- N.B. we cannot use the Real.sign function here because it is 0 at 0, but we need it to be -1.
lemma fDiv_statInfoFun_eq_StatInfo_of_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    fDiv (statInfoFun β γ) μ ν = statInfo μ ν (Bool.boolMeasure (.ofReal β) (.ofReal γ))
      + 2⁻¹ * (|β * (μ univ).toReal - γ * (ν univ).toReal|
        + (if γ ≤ β then -1 else 1) * (β * (μ univ).toReal - γ * (ν univ).toReal)) := by
  rcases le_or_lt γ β with (hβγ | hβγ)
  · rw [fDiv_statInfoFun_eq_StatInfo_of_nonneg_of_le hβ hγ hβγ, if_pos hβγ, neg_one_mul,
      EReal.neg_sub, add_comm (-_), sub_eq_add_neg, add_assoc]
    · exact Or.inl <| EReal.add_top_iff_ne_bot.mp rfl
    · exact Or.inl <| Ne.symm (ne_of_beq_false rfl)
  · rw [fDiv_statInfoFun_eq_StatInfo_of_nonneg_of_gt hβ hγ hβγ, if_neg hβγ.not_le, one_mul,
      add_sub_assoc]

lemma fDiv_statInfoFun_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv (statInfoFun β γ) μ ν ≠ ⊤ := by
  simp [derivAtTop_statInfoFun_ne_top, fDiv_ne_top_iff, integrable_statInfoFun_rnDeriv]

lemma integral_statInfoFun_curvatureMeasure (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    ∫ y, statInfoFun 1 y t ∂(curvatureMeasure f) = f t - f 1 - (rightDeriv f 1) * (t - 1) := by
  have : f t - f 1 - (rightDeriv f 1) * (t - 1) = ∫ x in (1)..t, t - x ∂(curvatureMeasure f) :=
    convex_taylor hf_cvx hf_cont
  rcases le_total t 1 with (ht | ht)
  · simp_rw [this, statInfoFun_of_one_of_right_le_one ht, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_ge ht, ← integral_neg, neg_sub]
  · simp_rw [this, statInfoFun_of_one_of_one_le_right ht, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_le ht]

lemma integral_statInfoFun_curvatureMeasure' (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f)
    (hf_one : f 1 = 0) (hfderiv_one : rightDeriv f 1 = 0) :
    ∫ y, statInfoFun 1 y t ∂(curvatureMeasure f) = f t := by
  rw [integral_statInfoFun_curvatureMeasure hf_cvx hf_cont, hf_one, hfderiv_one, sub_zero, zero_mul,
    sub_zero]

lemma lintegral_f_rnDeriv_eq_lintegralfDiv_statInfoFun_of_absolutelyContinuous
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f)
    (hf_one : f 1 = 0) (hfderiv_one : rightDeriv f 1 = 0) (h_ac : μ ≪ ν) :
    ∫⁻ x, ENNReal.ofReal (f ((∂μ/∂ν) x).toReal) ∂ν
      = ∫⁻ x, (fDiv (statInfoFun 1 x) μ ν).toENNReal ∂curvatureMeasure f  := by
  have h_meas : Measurable (fun x γ ↦ statInfoFun 1 γ ((∂μ/∂ν) x).toReal).uncurry :=
    stronglyMeasurable_statInfoFun.measurable.comp <|
      (measurable_const.prod_mk measurable_snd).prod_mk <|
      ((μ.measurable_rnDeriv ν).comp measurable_fst).ennreal_toReal
  classical
  simp_rw [fDiv_of_absolutelyContinuous h_ac, if_pos (integrable_statInfoFun_rnDeriv 1 _ _ _),
    EReal.real_coe_toENNReal,
    ← integral_statInfoFun_curvatureMeasure' hf_cvx hf_cont hf_one hfderiv_one]
  have (x : 𝒳) : ENNReal.ofReal (∫ γ, statInfoFun 1 γ ((∂μ/∂ν) x).toReal ∂curvatureMeasure f) =
      ∫⁻ γ, ENNReal.ofReal (statInfoFun 1 γ ((∂μ/∂ν) x).toReal) ∂curvatureMeasure f := by
    rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall fun y ↦ statInfoFun_nonneg _ _ _)
        h_meas.of_uncurry_left.stronglyMeasurable.aestronglyMeasurable]
    refine ENNReal.ofReal_toReal <| (lintegral_ofReal_le_lintegral_nnnorm _).trans_lt ?_ |>.ne
    exact (integrable_statInfoFun 1 _).hasFiniteIntegral
  simp_rw [this]
  rw [lintegral_lintegral_swap h_meas.ennreal_ofReal.aemeasurable]
  congr with y
  rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall fun _ ↦ statInfoFun_nonneg _ _ _)
    h_meas.of_uncurry_right.stronglyMeasurable.aestronglyMeasurable, ENNReal.ofReal_toReal]
  refine (integrable_toReal_iff ?_ ?_).mp ?_
  · exact h_meas.comp (f := fun x ↦ (x, y)) (by fun_prop) |>.ennreal_ofReal.aemeasurable
  · exact eventually_of_forall fun _ ↦ ENNReal.ofReal_ne_top
  · simp_rw [ENNReal.toReal_ofReal (statInfoFun_nonneg 1 _ _)]
    exact integrable_statInfoFun_rnDeriv 1 y μ ν

lemma fDiv_ne_top_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous'
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f)
    (hf_one : f 1 = 0) (hfderiv_one : rightDeriv f 1 = 0) (h_ac : μ ≪ ν) :
    fDiv f μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ (fDiv (statInfoFun 1 x) μ ν).toReal) (curvatureMeasure f) := by
  rw [fDiv_ne_top_iff]
  simp only [h_ac, implies_true, and_true]
  have (x : 𝒳) : f ((∂μ/∂ν) x).toReal = (ENNReal.ofReal (f ((∂μ/∂ν) x).toReal)).toReal := by
    refine (ENNReal.toReal_ofReal ?_).symm
    rw [← integral_statInfoFun_curvatureMeasure' hf_cvx hf_cont hf_one hfderiv_one]
    exact integral_nonneg fun _ ↦ statInfoFun_nonneg 1 _ _
  have : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (fun x ↦ (ENNReal.ofReal (f ((∂μ/∂ν) x).toReal)).toReal) ν := by
    simp_rw [← this]
  simp_rw [this, ← EReal.toReal_toENNReal fDiv_statInfoFun_nonneg]
  rw [integrable_toReal_iff]
  rotate_left
  · exact hf_cont.measurable.comp (Measure.measurable_rnDeriv μ ν).ennreal_toReal
      |>.ennreal_ofReal.aemeasurable
  · exact eventually_of_forall fun _ ↦ ENNReal.ofReal_ne_top
  rw [integrable_toReal_iff]
  rotate_left
  · exact (fDiv_statInfoFun_stronglyMeasurable μ ν).measurable.comp (f := fun x ↦ (1, x))
      (by fun_prop) |>.ereal_toENNReal.aemeasurable
  · exact eventually_of_forall fun _ ↦ EReal.toENNReal_ne_top_iff.mpr fDiv_statInfoFun_ne_top
  rw [lintegral_f_rnDeriv_eq_lintegralfDiv_statInfoFun_of_absolutelyContinuous hf_cvx hf_cont
    hf_one hfderiv_one h_ac]

lemma fDiv_ne_top_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (h_ac : μ ≪ ν) :
    fDiv f μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ (fDiv (statInfoFun 1 x) μ ν).toReal) (curvatureMeasure f) := by
  rw [fDiv_eq_fDiv_centeredFunction hf_cvx, EReal.add_ne_top_iff_of_ne_bot_of_ne_top]
  rotate_left
  · exact EReal.add_top_iff_ne_bot.mp rfl
  · exact Ne.symm (ne_of_beq_false rfl)
  rw [EReal.add_ne_top_iff_of_ne_bot_of_ne_top]
    <;> try {· simp [EReal.mul_ne_top, EReal.mul_ne_bot, measure_ne_top]}
  simp_rw [sub_eq_add_neg, ← neg_mul, mul_add, ← add_assoc]
  rw [fDiv_ne_top_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous' _ _ (by ring) _ h_ac,
    curvatureMeasure_add_const, curvatureMeasure_add_linear, curvatureMeasure_add_const]
  · exact (hf_cvx.add_const _).add (const_mul_id (-rightDeriv f 1)) |>.add_const _
  · exact ((hf_cont.add continuous_const).add (continuous_mul_left _)).add continuous_const
  · have hf_diff x := differentiableWithinAt_Ioi hf_cvx x
    rw [rightDeriv_add_const (by fun_prop), rightDeriv_add_linear (by fun_prop),
      rightDeriv_add_const hf_diff]
    simp

lemma integrable_f_rnDeriv_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (h_ac : μ ≪ ν) :
    Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (fun x ↦ (fDiv (statInfoFun 1 x) μ ν).toReal) (curvatureMeasure f) := by
  rw [← fDiv_ne_top_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous hf_cvx hf_cont h_ac]
  simp [fDiv_ne_top_iff, h_ac]

lemma fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous'
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (hf_one : f 1 = 0)
    (hfderiv_one : rightDeriv f 1 = 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ac : μ ≪ ν) :
    fDiv f μ ν = ∫ x, (fDiv (statInfoFun 1 x) μ ν).toReal ∂(curvatureMeasure f) := by
  classical
  rw [fDiv_of_absolutelyContinuous h_ac, if_pos h_int, EReal.coe_eq_coe_iff]
  simp_rw [fDiv_of_absolutelyContinuous h_ac, if_pos (integrable_statInfoFun_rnDeriv 1 _ _ _),
    EReal.toReal_coe,
    ← integral_statInfoFun_curvatureMeasure' hf_cvx hf_cont hf_one hfderiv_one]
  have h_meas : Measurable (fun x γ ↦ statInfoFun 1 γ ((∂μ/∂ν) x).toReal).uncurry :=
    stronglyMeasurable_statInfoFun.measurable.comp <|
      (measurable_const.prod_mk measurable_snd).prod_mk <|
      ((μ.measurable_rnDeriv ν).comp measurable_fst).ennreal_toReal
  have int_eq_lint : ∫ x, ∫ γ, statInfoFun 1 γ ((∂μ/∂ν) x).toReal ∂curvatureMeasure f ∂ν
      = (∫⁻ x, ∫⁻ γ, ENNReal.ofReal (statInfoFun 1 γ ((∂μ/∂ν) x).toReal)
        ∂curvatureMeasure f ∂ν).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    rotate_left
    · exact eventually_of_forall fun _ ↦ (integral_nonneg (fun _ ↦ statInfoFun_nonneg _ _ _))
    · refine (StronglyMeasurable.integral_prod_left ?_).aestronglyMeasurable
      exact (measurable_swap_iff.mpr h_meas).stronglyMeasurable
    congr with x
    rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall fun y ↦ statInfoFun_nonneg _ _ _)
      h_meas.of_uncurry_left.stronglyMeasurable.aestronglyMeasurable]
    refine ENNReal.ofReal_toReal <| (lintegral_ofReal_le_lintegral_nnnorm _).trans_lt ?_ |>.ne
    exact (integrable_statInfoFun 1 _).hasFiniteIntegral
  rw [int_eq_lint, lintegral_lintegral_swap h_meas.ennreal_ofReal.aemeasurable,
    integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact eventually_of_forall fun _ ↦ (integral_nonneg (fun _ ↦ statInfoFun_nonneg _ _ _))
  · exact h_meas.stronglyMeasurable.integral_prod_left.aestronglyMeasurable
  congr with γ
  rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall fun _ ↦ statInfoFun_nonneg _ _ _)
    h_meas.of_uncurry_right.stronglyMeasurable.aestronglyMeasurable, ENNReal.ofReal_toReal]
  have h_lt_top := (integrable_statInfoFun_rnDeriv 1 γ μ ν).hasFiniteIntegral
  simp_rw [HasFiniteIntegral, lt_top_iff_ne_top] at h_lt_top
  convert h_lt_top
  rw [← ENNReal.toReal_eq_toReal ENNReal.ofReal_ne_top ENNReal.coe_ne_top, toReal_coe_nnnorm,
    ENNReal.toReal_ofReal (statInfoFun_nonneg _ _ _),
    Real.norm_of_nonneg (statInfoFun_nonneg _ _ _)]

lemma fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) (h_ac : μ ≪ ν) :
    fDiv f μ ν = ∫ x, (fDiv (statInfoFun 1 x) μ ν).toReal ∂(curvatureMeasure f)
      + f 1 * ν univ + rightDeriv f 1 * (μ univ - ν univ) := by
  rw [fDiv_eq_fDiv_centeredFunction hf_cvx]
  congr
  · have h : ConvexOn ℝ univ (fun x ↦ f x - f 1 - rightDeriv f 1 * (x - 1)) := by
      simp_rw [mul_sub, sub_eq_add_neg, neg_add, neg_neg, ← neg_mul]
      exact (hf_cvx.add_const _).add ((ConvexOn.const_mul_id _).add (convexOn_const _ convex_univ))
    rw [fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous'
      h (by continuity) (by simp) _ _ h_ac]
    · simp_rw [mul_sub, sub_eq_add_neg, neg_add, neg_neg, ← neg_mul, ← add_assoc,
        curvatureMeasure_add_const, curvatureMeasure_add_linear, curvatureMeasure_add_const]
    · have hf_diff x := differentiableWithinAt_Ioi hf_cvx x
      simp_rw [mul_sub, sub_eq_add_neg, neg_add, neg_neg, ← neg_mul, ← add_assoc]
      rw [rightDeriv_add_const (by fun_prop), rightDeriv_add_linear (by fun_prop),
        rightDeriv_add_const hf_diff]
      simp
    · exact (h_int.sub (integrable_const _)).sub
        ((Measure.integrable_toReal_rnDeriv.sub (integrable_const 1)).const_mul _)
  all_goals exact ENNReal.toReal_toEReal_of_ne_top (measure_ne_top _ _)

lemma fDiv_eq_lintegral_fDiv_statInfoFun_of_absolutelyContinuous [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (h_ac : μ ≪ ν) :
    fDiv f μ ν = ∫⁻ x, (fDiv (statInfoFun 1 x) μ ν).toENNReal ∂(curvatureMeasure f)
      + f 1 * ν univ + rightDeriv f 1 * (μ univ - ν univ) := by
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous hf_cvx hf_cont h_int h_ac,
      integral_eq_lintegral_of_nonneg_ae]
    rotate_left
    · exact eventually_of_forall <| fun _ ↦ EReal.toReal_nonneg fDiv_statInfoFun_nonneg
    · exact (fDiv_statInfoFun_stronglyMeasurable μ ν).measurable.comp (f := fun x ↦ (1, x))
        (by fun_prop) |>.ereal_toReal.aestronglyMeasurable
    simp_rw [← EReal.toENNReal_of_ne_top fDiv_statInfoFun_ne_top]
    rw [ENNReal.toReal_toEReal_of_ne_top]
    rw [integrable_f_rnDeriv_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous hf_cvx
      hf_cont h_ac] at h_int
    refine (integrable_toReal_iff ?_ ?_).mp ?_
    · exact (fDiv_statInfoFun_stronglyMeasurable μ ν).measurable.comp (f := fun x ↦ (1, x))
        (by fun_prop) |>.ereal_toENNReal.aemeasurable
    · exact eventually_of_forall fun _ ↦ EReal.toENNReal_ne_top_iff.mpr fDiv_statInfoFun_ne_top
    simp_rw [EReal.toReal_toENNReal fDiv_statInfoFun_nonneg, h_int]
  · classical
    rw [fDiv_of_absolutelyContinuous h_ac, if_neg h_int]
    convert (EReal.top_add_of_ne_bot ?_).symm
    swap
    · simp [sub_eq_add_neg, measure_ne_top, EReal.add_ne_top, EReal.add_ne_bot, EReal.mul_ne_bot]
    convert EReal.top_add_of_ne_bot ?_
    swap; · simp [measure_ne_top, EReal.mul_ne_bot]
    simp_rw [EReal.coe_ennreal_eq_top_iff]
    have h := integrable_f_rnDeriv_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous
      hf_cvx hf_cont h_ac |>.mpr.mt h_int
    contrapose! h
    simp_rw [← EReal.toReal_toENNReal fDiv_statInfoFun_nonneg]
    refine (integrable_toReal_iff ?_ ?_).mpr h
    · exact (fDiv_statInfoFun_stronglyMeasurable μ ν).measurable.comp (f := fun x ↦ (1, x))
        (by fun_prop) |>.ereal_toENNReal.aemeasurable
    · exact eventually_of_forall fun _ ↦ EReal.toENNReal_ne_top_iff.mpr fDiv_statInfoFun_ne_top

lemma lintegral_statInfoFun_one_zero (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    ∫⁻ x, ENNReal.ofReal (statInfoFun 1 x 0) ∂curvatureMeasure f
      = (f 0).toEReal - f 1 + rightDeriv f 1 := by
  norm_cast
  have := convex_taylor hf_cvx hf_cont (a := 1) (b := 0)
  simp only [zero_sub, mul_neg, mul_one, sub_neg_eq_add] at this
  rw [this, intervalIntegral.integral_of_ge (zero_le_one' _), integral_neg, neg_neg,
    ← ofReal_integral_eq_lintegral_ofReal _
    (eventually_of_forall fun x ↦ statInfoFun_nonneg 1 x 0)]
  rotate_left
  · refine Integrable.mono' (g := (Ioc 0 1).indicator 1) ?_
      measurable_statInfoFun2.aestronglyMeasurable ?_
    · exact IntegrableOn.integrable_indicator
        (integrableOn_const.mpr (Or.inr measure_Ioc_lt_top)) measurableSet_Ioc
    · simp_rw [Real.norm_of_nonneg (statInfoFun_nonneg 1 _ 0),
        statInfoFun_of_one_of_right_le_one zero_le_one, sub_zero]
      exact eventually_of_forall fun x ↦ Set.indicator_le_indicator' fun hx ↦ hx.2
  rw [EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg_of_ae <| eventually_of_forall
    fun x ↦ statInfoFun_nonneg 1 x 0), ← integral_indicator measurableSet_Ioc]
  simp_rw [statInfoFun_of_one_of_right_le_one zero_le_one, sub_zero]

lemma fDiv_eq_lintegral_fDiv_statInfoFun_of_mutuallySingular [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (h_ms : μ ⟂ₘ ν) :
    fDiv f μ ν = ∫⁻ x, (fDiv (statInfoFun 1 x) μ ν).toENNReal ∂(curvatureMeasure f)
      + f 1 * ν univ + rightDeriv f 1 * (μ univ - ν univ) := by
  have hf_cvx' : ConvexOn ℝ (Ici 0) f := (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0))
  have h1 : ∫⁻ x, (statInfoFun 1 x 0 * (ν univ).toEReal
        + derivAtTop (statInfoFun 1 x) * μ univ).toENNReal ∂curvatureMeasure f
      = (∫⁻ x, ENNReal.ofReal (statInfoFun 1 x 0) ∂curvatureMeasure f) * ν univ
        + (∫⁻ x, (derivAtTop (statInfoFun 1 x)).toENNReal ∂curvatureMeasure f) * μ univ := by
    rw [← lintegral_mul_const _ (Measurable.ennreal_ofReal measurable_statInfoFun2),
      ← lintegral_mul_const _]
    swap
    · simp_rw [derivAtTop_statInfoFun_eq]
      refine (Measurable.ite (.const _) ?_ ?_).coe_real_ereal.ereal_toENNReal <;>
      · refine Measurable.ite (measurableSet_le (fun _ a ↦ a) ?_) ?_ ?_ <;> exact measurable_const
    rw [← lintegral_add_left]
    swap; · exact measurable_statInfoFun2.ennreal_ofReal.mul_const _
    congr with x
    rw [EReal.toENNReal_add]
    rotate_left
    · exact mul_nonneg (EReal.coe_nonneg.mpr (statInfoFun_nonneg 1 x 0))
        (EReal.coe_ennreal_nonneg _)
    · exact mul_nonneg (derivAtTop_statInfoFun_nonneg 1 x) (EReal.coe_ennreal_nonneg _)
    rw [EReal.toENNReal_mul (EReal.coe_nonneg.mpr <| statInfoFun_nonneg 1 x 0),
      EReal.toENNReal_mul (derivAtTop_statInfoFun_nonneg 1 x)]
    simp [-statInfoFun_of_one]
  have h2 : ∫⁻ x, (derivAtTop (statInfoFun 1 x)).toENNReal ∂curvatureMeasure f
      = (derivAtTop f - rightDeriv f 1).toENNReal := by
    calc
      _ = curvatureMeasure f (Ioi 1) := by
        simp_rw [derivAtTop_statInfoFun_eq, ← lintegral_indicator_one measurableSet_Ioi]
        congr with x
        by_cases h : x ∈ Ioi 1
        · simpa [h]
        · simp [h, show x ≤ 1 from le_of_not_lt h]
      _ = (derivAtTop f - rightDeriv f 1).toENNReal := by
        rw [curvatureMeasure_of_convexOn hf_cvx]
        by_cases h_top : derivAtTop f = ⊤
        · rw [h_top, EReal.top_sub_coe, EReal.toENNReal_top,
            StieltjesFunction.measure_Ioi_of_tendsto_atTop_atTop]
          exact hf_cvx'.derivAtTop_eq_top_iff.mp h_top
        · lift (derivAtTop f) to ℝ using ⟨h_top, hf_cvx'.derivAtTop_ne_bot⟩ with x hx
          rw [StieltjesFunction.measure_Ioi _ ?_ 1 (l := x)]
          · norm_cast
          exact (hx ▸ hf_cvx'.tendsto_toReal_derivAtTop (hx ▸ h_top) :)
  simp_rw [fDiv_of_mutuallySingular h_ms, h1]
  push_cast
  rw [lintegral_statInfoFun_one_zero hf_cvx hf_cont, h2, EReal.coe_toENNReal]
  swap
  · rw [EReal.sub_nonneg (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    exact rightDeriv_le_derivAtTop hf_cvx' zero_lt_one
  simp_rw [sub_eq_add_neg, ← ENNReal.toReal_toEReal_of_ne_top (measure_ne_top ν _),
    ← ENNReal.toReal_toEReal_of_ne_top (measure_ne_top μ _),
    EReal.add_mul_coe_of_nonneg ENNReal.toReal_nonneg, ← EReal.coe_neg (ν univ).toReal,
    ← EReal.coe_add, ← EReal.coe_mul _ (_ + _), mul_add, EReal.coe_add, neg_mul, ← EReal.coe_mul,
    mul_neg, EReal.coe_neg, add_assoc]
  congr
  simp_rw [add_comm (rightDeriv f 1 * (ν _).toReal).toEReal, add_assoc,
    add_comm _ (rightDeriv f 1 * _).toEReal, ← add_assoc, ← sub_eq_add_neg,
    EReal.add_sub_cancel_right, sub_eq_add_neg, add_assoc, add_comm _ (_ + (_ + (_ + _))),
    add_comm (f 1 * _).toEReal, ← add_assoc, ← sub_eq_add_neg, EReal.add_sub_cancel_right,
    sub_eq_add_neg, add_assoc, add_comm (-(rightDeriv f 1 * _).toEReal), ← add_assoc,
    ← sub_eq_add_neg, EReal.add_sub_cancel_right]

lemma fDiv_eq_lintegral_fDiv_statInfoFun [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    fDiv f μ ν = ∫⁻ x, (fDiv (statInfoFun 1 x) μ ν).toENNReal ∂(curvatureMeasure f)
      + f 1 * ν univ + rightDeriv f 1 * (μ univ - ν univ) := by
  rw [fDiv_eq_add_withDensity_singularPart _ _ (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0)),
    fDiv_eq_lintegral_fDiv_statInfoFun_of_mutuallySingular hf_cvx hf_cont
    (μ.mutuallySingular_singularPart ν), fDiv_eq_lintegral_fDiv_statInfoFun_of_absolutelyContinuous
    hf_cvx hf_cont (withDensity_absolutelyContinuous ν (∂μ/∂ν))]
  have h1 : ∫⁻ x, (fDiv (statInfoFun 1 x) μ ν).toENNReal ∂curvatureMeasure f
      = ∫⁻ x, (fDiv (statInfoFun 1 x) (ν.withDensity (∂μ/∂ν)) ν).toENNReal ∂curvatureMeasure f
        + ∫⁻ x, (fDiv (statInfoFun 1 x) (μ.singularPart ν) ν).toENNReal ∂curvatureMeasure f
        - (∫⁻ x, .ofReal (statInfoFun 1 x 0) ∂curvatureMeasure f : EReal) * (ν univ).toReal := by
    have h_nonneg (x : ℝ) : 0 ≤ fDiv (statInfoFun 1 x) μ ν := fDiv_statInfoFun_nonneg
    simp_rw [fDiv_eq_add_withDensity_singularPart μ ν ((convexOn_statInfoFun 1 _).subset
      (fun _ _ ↦ trivial) (convex_Ici 0))] at h_nonneg ⊢
    rw_mod_cast [← lintegral_add_left]
    swap; · exact ((fDiv_statInfoFun_stronglyMeasurable (ν.withDensity (∂μ/∂ν)) ν).measurable.comp
      (by fun_prop) (f := fun x ↦ (1, x))).ereal_toENNReal
    simp_rw [← EReal.toENNReal_add fDiv_statInfoFun_nonneg fDiv_statInfoFun_nonneg]
    have h_ne_top : (∫⁻ x, .ofReal (statInfoFun 1 x 0) ∂curvatureMeasure f) * ν univ ≠ ⊤ := by
      refine ENNReal.mul_ne_top (lt_top_iff_ne_top.mp ?_) (measure_ne_top ν _)
      calc
        _ ≤ ∫⁻ x, (Ioc 0 1).indicator 1 x ∂curvatureMeasure f := by
          simp_rw [statInfoFun_of_one_of_right_le_one zero_le_one, sub_zero]
          refine lintegral_mono (le_indicator ?_ ?_) <;> simp_all
        _ < _ := by
          rw [lintegral_indicator_one measurableSet_Ioc]
          exact measure_Ioc_lt_top
    have h_le (x : ℝ) : .ofReal (statInfoFun 1 x 0) * ν univ
        ≤ (fDiv (statInfoFun 1 x) (ν.withDensity (∂μ/∂ν)) ν
          + fDiv (statInfoFun 1 x) (μ.singularPart ν) ν).toENNReal := by
      rw [← EReal.real_coe_toENNReal, ← EReal.toENNReal_coe (x := ν _),
        ← EReal.toENNReal_mul (EReal.coe_nonneg.mpr <| statInfoFun_nonneg 1 x 0)]
      refine EReal.toENNReal_le_toENNReal <| (EReal.sub_nonneg ?_ ?_).mp (h_nonneg x)
        <;> simp [EReal.mul_ne_top, EReal.mul_ne_bot, measure_ne_top ν univ]
    rw [ENNReal.toReal_toEReal_of_ne_top (measure_ne_top ν _), ← EReal.coe_ennreal_mul,
      ← ENNReal.toEReal_sub h_ne_top]
    swap
    · exact lintegral_mul_const' _ _ (measure_ne_top ν _) ▸ lintegral_mono fun x ↦ h_le x
    rw [← lintegral_mul_const' _ _ (measure_ne_top ν _),
      ← lintegral_sub (measurable_statInfoFun2.ennreal_ofReal.mul_const _)
      (lintegral_mul_const' _ _ (measure_ne_top ν _) ▸ h_ne_top)
      (eventually_of_forall fun x ↦ h_le x)]
    congr with x
    rw [EReal.toENNReal_sub (mul_nonneg (EReal.coe_nonneg.mpr (statInfoFun_nonneg 1 x 0))
      (EReal.coe_ennreal_nonneg _)),
      EReal.toENNReal_mul (EReal.coe_nonneg.mpr (statInfoFun_nonneg 1 x 0)), EReal.toENNReal_coe]
    congr
  simp_rw [h1, lintegral_statInfoFun_one_zero hf_cvx hf_cont, sub_eq_add_neg, add_assoc]
  congr 1
  simp_rw [add_comm (- (((f 0).toEReal + _) * _)), add_comm (∫⁻ _, _ ∂_).toEReal _, ← add_assoc,
    ← ENNReal.toReal_toEReal_of_ne_top (measure_ne_top _ _)]
  norm_cast
  ring_nf
  simp_rw [sub_eq_add_neg, mul_assoc, ← mul_neg, ← mul_add]
  congr 1
  nth_rw 3 [μ.haveLebesgueDecomposition_add ν]
  rw [Measure.coe_add, Pi.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring_nf

end StatInfoFun

section DataProcessingInequality

/-- **Data processing inequality** for the f-divergence of `statInfoFun`. -/
lemma fDiv_statInfoFun_comp_right_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] (hβ : 0 ≤ β) :
    fDiv (statInfoFun β γ) (η ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv (statInfoFun β γ) μ ν := by
  rcases le_total γ 0 with (hγ | hγ)
  · rw [fDiv_statInfoFun_eq_zero_of_nonneg_of_nonpos hβ hγ,
      fDiv_statInfoFun_eq_zero_of_nonneg_of_nonpos hβ hγ]
  simp_rw [fDiv_statInfoFun_eq_StatInfo_of_nonneg hβ hγ]
  gcongr ?_ + ?_
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr <| statInfo_comp_le _ _ _ _
  · simp_rw [Measure.comp_apply_univ, le_refl]

-- The name is `fDiv_comp_right_le'`, since there is already `fDiv_comp_right_le` in the `fDiv.CompProd` file.
/-- **Data processing inequality** for the f-divergence. -/
lemma fDiv_comp_right_le' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    fDiv f (η ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv f μ ν := by
  simp_rw [fDiv_eq_lintegral_fDiv_statInfoFun hf_cvx hf_cont, Measure.comp_apply_univ]
  gcongr
  simp only [EReal.coe_ennreal_le_coe_ennreal_iff]
  exact lintegral_mono fun x ↦ EReal.toENNReal_le_toENNReal <|
    fDiv_statInfoFun_comp_right_le η zero_le_one

lemma le_fDiv_compProd' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel 𝒳 𝒳') [IsMarkovKernel κ] [IsMarkovKernel η] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    fDiv f μ ν ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  nth_rw 1 [← Measure.fst_compProd μ κ, ← Measure.fst_compProd ν η]
  simp_rw [Measure.fst, ← Measure.comp_deterministic_eq_map measurable_fst]
  exact fDiv_comp_right_le' _ hf_cvx hf_cont

lemma fDiv_compProd_right' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel 𝒳 𝒳') [IsMarkovKernel κ] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = fDiv f μ ν := by
  refine le_antisymm ?_ (le_fDiv_compProd' κ κ hf_cvx hf_cont)
  simp_rw [Measure.compProd_eq_comp]
  exact fDiv_comp_right_le' _ hf_cvx hf_cont

lemma fDiv_comp_le_compProd' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel 𝒳 𝒳') [IsMarkovKernel κ] [IsMarkovKernel η] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  nth_rw 1 [← Measure.snd_compProd μ κ, ← Measure.snd_compProd ν η]
  simp_rw [Measure.snd, ← Measure.comp_deterministic_eq_map measurable_snd]
  exact fDiv_comp_right_le' _ hf_cvx hf_cont

lemma fDiv_comp_le_compProd_right' [IsFiniteMeasure μ]
    (κ η : Kernel 𝒳 𝒳') [IsMarkovKernel κ] [IsMarkovKernel η] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ μ) ≤ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) :=
  fDiv_comp_le_compProd' κ η hf_cvx hf_cont

lemma fDiv_fst_le' (μ ν : Measure (𝒳 × 𝒳')) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    fDiv f μ.fst ν.fst ≤ fDiv f μ ν := by
  simp_rw [Measure.fst, ← Measure.comp_deterministic_eq_map measurable_fst]
  exact fDiv_comp_right_le' _ hf_cvx hf_cont

lemma fDiv_snd_le' (μ ν : Measure (𝒳 × 𝒳')) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    fDiv f μ.snd ν.snd ≤ fDiv f μ ν := by
  simp_rw [Measure.snd, ← Measure.comp_deterministic_eq_map measurable_snd]
  exact fDiv_comp_right_le' _ hf_cvx hf_cont

end DataProcessingInequality

end ProbabilityTheory

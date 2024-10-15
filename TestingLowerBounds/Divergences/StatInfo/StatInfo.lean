/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.IntegrableFRNDeriv
import TestingLowerBounds.Divergences.StatInfo.StatInfoFun
import TestingLowerBounds.Testing.Binary
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
    <| ENNReal.mul_lt_top (measure_lt_top π _) (measure_lt_top μ _)).ne

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
    (Measurable.of_discrete.comp' (measurable_one.indicator hE))
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

lemma toReal_statInfo_eq_integral_max_of_ge [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure π] (h : π {true} * ν univ ≤ π {false} * μ univ) :
    (statInfo μ ν π).toReal
      = ∫ x, max 0 ((π {true}).toReal - (π {false} * (∂μ/∂ν) x).toReal) ∂ν := by
  by_cases h_false : π {false} = 0
  · simp only [h_false, zero_mul, nonpos_iff_eq_zero, mul_eq_zero, Measure.measure_univ_eq_zero]
      at h
    rcases h with (h | h)
    · simp [show π = 0 from Measure.measure_bool_ext h_false h]
    · simp [h]
  by_cases h_true : π {true} = 0
  · have (x : 𝒳) : 0 ≥ -((π {false}).toReal * ((∂μ/∂ν) x).toReal) := neg_nonpos.mpr (by positivity)
    simp [statInfo, h_true, bayesBinaryRisk_of_measure_true_eq_zero, max_eq_left (this _)]
  have hνac : ν ≪ (twoHypKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_measure_comp_twoHypKernel_right μ ν h_true
  rw [toReal_statInfo_eq_min_sub_integral, min_eq_right ((ENNReal.toReal_le_toReal _ _).mpr h)]
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
  rcases le_total (π {false} * μ univ) (π {true} * ν univ) with (h | h)
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
    · refine sub_nonneg.mpr <| (ENNReal.toReal_le_toReal ?_ ?_).mpr h
        <;> try simp only [ne_eq, measure_ne_top _ _, not_false_eq_true, ENNReal.mul_ne_top]
    simp_rw [toReal_statInfo_eq_integral_max_of_ge h, max_eq_add_add_abs_sub, zero_add, zero_sub,
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

lemma integrable_statInfoFun_rnDeriv (β γ : ℝ)
    (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x ↦ statInfoFun β γ ((∂μ/∂ν) x).toReal) ν := by
  refine integrable_f_rnDeriv_of_derivAtTop_ne_top _ _ stronglyMeasurable_statInfoFun3
    ?_ (derivAtTop_statInfoFun_ne_top β γ)
  exact (convexOn_statInfoFun β γ).subset (fun _ _ ↦ trivial) (convex_Ici 0)

end ProbabilityTheory

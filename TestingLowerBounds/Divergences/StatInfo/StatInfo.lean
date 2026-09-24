/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import TestingLowerBounds.IntegrableFRNDeriv
public import TestingLowerBounds.Divergences.StatInfo.StatInfoFun
public import TestingLowerBounds.Testing.Binary
public import TestingLowerBounds.ForMathlib.ENNReal
/-!
# Statistical information

## Main definitions

* `statInfo μ ν π`: the statistical information of the measures `μ` and `ν` with respect to the
  prior `π` on `Bool`, the difference between the Bayes risks of the testing problem without and
  with observations.

## Main statements

* `statInfo_comp_le`: data-processing inequality.
* `toReal_statInfo_eq_integral_max_of_le`, `toReal_statInfo_eq_integral_max_of_ge`,
  `toReal_statInfo_eq_integral_abs`: integral forms of the statistical information.

-/

@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞} {π : Measure Bool} {f : ℝ → ℝ} {β γ x t : ℝ}

/-- The statistical information of the measures `μ` and `ν` with respect to
the prior `π ∈ ℳ({0,1})`. -/
noncomputable
def statInfo (μ ν : Measure 𝒳) (π : Measure Bool) : ℝ≥0∞ :=
  bayesBinaryRisk ((Kernel.discard 𝒳 : Kernel 𝒳 PUnit.{1}) ∘ₘ μ)
    ((Kernel.discard 𝒳 : Kernel 𝒳 PUnit.{1}) ∘ₘ ν) π - bayesBinaryRisk μ ν π

lemma statInfo_eq_min_sub (μ ν : Measure 𝒳) (π : Measure Bool) :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ) - bayesBinaryRisk μ ν π := by
  simp_rw [statInfo, Measure.discard_comp, bayesBinaryRisk_dirac]

lemma statInfo_eq_riskIncrease (μ ν : Measure 𝒳) (π : Measure Bool) :
    statInfo μ ν π = riskIncrease simpleBinaryLoss (Kernel.boolKernel μ ν) π := by
  simp_rw [statInfo, bayesBinaryRisk, riskIncrease, Kernel.comp_boolKernel]

@[simp] lemma statInfo_zero_left : statInfo 0 ν π = 0 := by simp [statInfo]

@[simp] lemma statInfo_zero_right : statInfo μ 0 π = 0 := by simp [statInfo]

@[simp] lemma statInfo_zero_prior : statInfo μ ν 0 = 0 := by simp [statInfo]

@[simp] lemma statInfo_self : statInfo μ μ π = 0 := by simp [statInfo]

lemma statInfo_le_min : statInfo μ ν π ≤ min (π {false} * μ univ) (π {true} * ν univ) :=
  statInfo_eq_min_sub μ ν π ▸ tsub_le_self

lemma statInfo_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure π] :
    statInfo μ ν π ≠ ∞ :=
  (statInfo_le_min.trans_lt <| min_lt_iff.mpr <| Or.inl
    <| ENNReal.mul_lt_top (measure_lt_top π _) (measure_lt_top μ _)).ne

lemma statInfo_symm : statInfo μ ν π = statInfo ν μ (π.map Bool.not) := by
  simp_rw [statInfo, bayesBinaryRisk_symm _ _ π]

lemma statInfo_of_measure_true_eq_zero (μ ν : Measure 𝒳) (hπ : π {true} = 0) :
    statInfo μ ν π = 0 :=
  le_antisymm (statInfo_le_min.trans (by simp [hπ])) zero_le

lemma statInfo_of_measure_false_eq_zero (μ ν : Measure 𝒳) (hπ : π {false} = 0) :
    statInfo μ ν π = 0 :=
  le_antisymm (statInfo_le_min.trans (by simp [hπ])) zero_le

/-- **Data processing inequality** for the statistical information. -/
lemma statInfo_comp_le (μ ν : Measure 𝒳) (π : Measure Bool) (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] :
    statInfo (η ∘ₘ μ) (η ∘ₘ ν) π ≤ statInfo μ ν π := by
  refine tsub_le_tsub ?_ (bayesBinaryRisk_le_bayesBinaryRisk_comp _ _ _ _)
  simp [Measure.bind_apply .univ (Kernel.measurable _).aemeasurable]

lemma statInfo_boolMeasure_le_statInfo {E : Set 𝒳} (hE : MeasurableSet E) :
    statInfo (Bool.boolMeasure (μ Eᶜ) (μ E)) (Bool.boolMeasure (ν Eᶜ) (ν E)) π
      ≤ statInfo μ ν π := by
  have h_meas : Measurable fun x ↦ Bool.ofNat (E.indicator 1 x) :=
    (Measurable.of_discrete.fun_comp (measurable_one.indicator hE))
  let η : Kernel 𝒳 Bool := Kernel.deterministic (fun x ↦ Bool.ofNat (E.indicator 1 x)) h_meas
  have h_false : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {false} = Eᶜ := by
    ext x; simp [Bool.ofNat]
  have h_true : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {true} = E := by
    ext x; simp [Bool.ofNat]
  convert statInfo_comp_le μ ν π η <;>
  · ext
    · rw [Measure.deterministic_comp_eq_map, Measure.map_apply h_meas (by trivial), h_false,
        Bool.boolMeasure_apply_false]
    · rw [Measure.deterministic_comp_eq_map, Measure.map_apply h_meas (by trivial), h_true,
        Bool.boolMeasure_apply_true]

lemma statInfo_eq_min_sub_lintegral (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ∫⁻ x, min (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x)
      (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x) ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  rw [statInfo_eq_min_sub, bayesBinaryRisk_eq_lintegral_min]

lemma statInfo_eq_min_sub_lintegral' {ζ : Measure 𝒳} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SigmaFinite ζ] (π : Measure Bool) [IsFiniteMeasure π] (hμζ : μ ≪ ζ) (hνζ : ν ≪ ζ) :
    statInfo μ ν π = min (π {false} * μ univ) (π {true} * ν univ)
      - ∫⁻ x, min (π {false} * (∂μ/∂ζ) x) (π {true} * (∂ν/∂ζ) x) ∂ζ := by
  by_cases h_false : π {false} = 0
  · simp [statInfo, h_false, bayesBinaryRisk_of_measure_false_eq_zero]
  by_cases h_true : π {true} = 0
  · simp [statInfo, h_true, bayesBinaryRisk_of_measure_true_eq_zero]
  have hμac : μ ≪ (Kernel.boolKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_boolKernel_comp_left μ ν h_false
  have hνac : ν ≪ (Kernel.boolKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_boolKernel_comp_right μ ν h_true
  have hacζ : (Kernel.boolKernel μ ν ∘ₘ π) ≪ ζ :=
    boolKernel_comp_measure _ _ _ ▸ (hνζ.smul_left _).add_left (hμζ.smul_left _)
  rw [statInfo_eq_min_sub_lintegral, ← lintegral_rnDeriv_mul hacζ (by fun_prop)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv hμac, Measure.rnDeriv_mul_rnDeriv hνac] with x hxμ hxν
  rw [mul_min, mul_comm, mul_comm _ (π _ * _), mul_assoc, mul_assoc]
  congr

lemma toReal_statInfo_eq_min_sub_integral (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    (statInfo μ ν π).toReal = min (π {false} * μ univ).toReal (π {true} * ν univ).toReal
      - ∫ x, min (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
      (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
        ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  have hμ : π {false} * μ univ ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top μ _)
  have hν : π {true} * ν univ ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top ν _)
  rw [statInfo_eq_min_sub, ENNReal.toReal_sub_of_le (bayesBinaryRisk_le_min μ ν π)]
  swap; · simp only [ne_eq, min_eq_top, hμ, hν, and_self, not_false_eq_true]
  rw [toReal_bayesBinaryRisk_eq_integral_min,
    MonotoneOn.map_min (fun _ _ _ hb hab ↦ ENNReal.toReal_mono hb hab) hμ hν]

lemma toReal_statInfo_eq_integral_max_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure π] (h : π {false} * μ univ ≤ π {true} * ν univ) :
    (statInfo μ ν π).toReal
      = ∫ x, max 0 ((π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal) ∂ν
        + (π {false} * μ.singularPart ν univ).toReal := by
  by_cases h_false : π {false} = 0
  · simp [statInfo, h_false, bayesBinaryRisk_of_measure_false_eq_zero]
  by_cases h_true : π {true} = 0
  · simp only [h_true, zero_mul, nonpos_iff_eq_zero, mul_eq_zero, Measure.measure_univ_eq_zero,
      statInfo, Measure.discard_comp, bayesBinaryRisk_of_measure_true_eq_zero, tsub_self,
      ENNReal.toReal_zero, ENNReal.toReal_mul, sub_zero] at h ⊢
    rcases h with (h | h)
    · simp [h]
    · rw [integral_congr_ae (g := 0)]
      swap
      · filter_upwards [ν.rnDeriv_zero] with x hx
        simp [h, hx]
      simp [h]
  have hμac : μ ≪ (Kernel.boolKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_boolKernel_comp_left μ ν h_false
  have hνac : ν ≪ (Kernel.boolKernel μ ν ∘ₘ π) :=
    absolutelyContinuous_boolKernel_comp_right μ ν h_true
  rw [toReal_statInfo_eq_min_sub_integral, min_eq_left ((ENNReal.toReal_le_toReal _ _).mpr h)]
    <;> try simp only [ne_eq, measure_ne_top _ _, not_false_eq_true, ENNReal.mul_ne_top]
  let s := μ.singularPartSet ν
  have hs : MeasurableSet s := Measure.measurableSet_singularPartSet
  calc
    _ = (π {false} * μ univ).toReal
        - ∫ x, (π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal
          + min 0 ((π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal
            - (π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal)
              ∂Kernel.boolKernel μ ν ∘ₘ π := by
      congr with x
      nth_rw 1 [← add_zero (π _ * _).toReal, ← add_sub_cancel_left
        (π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal (π {true} * _).toReal]
      rw [add_sub_assoc, min_add_add_left]
    _ = (π {false} * μ univ).toReal
        - (∫ x, (π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal ∂Kernel.boolKernel μ ν ∘ₘ π
        + ∫ x, min 0 ((π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal
            - (π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal)
              ∂Kernel.boolKernel μ ν ∘ₘ π) := by
      simp_rw [ENNReal.toReal_mul]
      congr
      refine integral_add (Integrable.const_mul Measure.integrable_toReal_rnDeriv _) ?_
      refine (integrable_zero _ _ _).inf (Integrable.sub ?_ ?_) <;>
      · exact Measure.integrable_toReal_rnDeriv.const_mul _
    _ = - ∫ x, min 0 ((π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal
          - (π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal)
            ∂Kernel.boolKernel μ ν ∘ₘ π := by
      simp_rw [ENNReal.toReal_mul, ← sub_sub, sub_eq_neg_self, sub_eq_zero, integral_const_mul,
        Measure.integral_toReal_rnDeriv hμac, ← measureReal_def]
    _ = ∫ x, max 0 ((π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal
        - (π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal) ∂Kernel.boolKernel μ ν ∘ₘ π := by
      simp [← integral_neg, neg_inf]
    _ = ∫ x in s, max 0 ((π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal
          - (π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal) ∂Kernel.boolKernel μ ν ∘ₘ π
        + ∫ x in sᶜ, max 0 ((π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal
          - (π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal)
            ∂Kernel.boolKernel μ ν ∘ₘ π := by
      simp_rw [ENNReal.toReal_mul]
      refine integral_add_compl hs ((integrable_zero _ _ _).sup (Integrable.sub ?_ ?_)) |>.symm <;>
      · exact Measure.integrable_toReal_rnDeriv.const_mul _
    _ = ∫ x in s, max 0 (π {false} * (∂(μ.singularPart ν)/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal
          ∂Kernel.boolKernel μ ν ∘ₘ π
        + ∫ x in sᶜ, (max 0
            ((π {false} * (∂μ.restrict (μ.singularPartSet ν)ᶜ/∂ν) x).toReal - (π {true}).toReal))
          * ((∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal ∂Kernel.boolKernel μ ν ∘ₘ π := by
      congr 1
      · apply setIntegral_congr_ae hs
        filter_upwards [μ.rnDeriv_eq_zero_ae_of_singularPartSet ν _,
          (μ.singularPart ν).rnDeriv_add' (ν.withDensity (μ.rnDeriv ν))
            (Kernel.boolKernel μ ν ∘ₘ π),
          Measure.rnDeriv_withDensity_left_of_absolutelyContinuous hνac
          (μ.measurable_rnDeriv ν).aemeasurable] with x hx1 hx2 hx3
        intro hxs
        nth_rw 1 [← μ.singularPart_add_rnDeriv ν]
        simp_rw [hx2, Pi.add_apply, hx3, hx1 hxs, mul_zero, ENNReal.toReal_zero, sub_zero, add_zero]
      · apply setIntegral_congr_ae hs.compl
        filter_upwards [μ.rnDeriv_restrict (Kernel.boolKernel μ ν ∘ₘ π) hs.compl,
          Measure.rnDeriv_mul_rnDeriv
          (μ.absolutelyContinuous_restrict_compl_singularPartSet ν)] with x hx1 hx2 hxs
        rw [max_mul_of_nonneg _ _ ENNReal.toReal_nonneg, zero_mul, sub_mul]
        rw [Set.indicator_of_mem hxs] at hx1
        simp only [s] at hx1
        simp_rw [ENNReal.toReal_mul, mul_assoc, ← hx1, ← hx2, Pi.mul_apply, ENNReal.toReal_mul]
    _ = ∫ x, max 0 (π {false} * (∂(μ.singularPart ν)/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal
          ∂Kernel.boolKernel μ ν ∘ₘ π
        + ∫ x in sᶜ, (max 0 ((π {false}
          * (∂μ.restrict (μ.singularPartSet ν)ᶜ/∂ν) x).toReal - (π {true}).toReal)) ∂ν := by
      congr 1
      · nth_rw 2 [← integral_add_compl hs]
        swap
        · simp_rw [ENNReal.toReal_mul]
          exact ((integrable_zero _ _ _).sup (Measure.integrable_toReal_rnDeriv.const_mul _))
        refine left_eq_add.mpr <| setIntegral_eq_zero_of_ae_eq_zero ?_
        filter_upwards [μ.rnDeriv_restrict _ hs] with x hx
        intro hxs
        rw [← Measure.restrict_singularPartSet_eq_singularPart, hx, indicator_of_notMem hxs,
          mul_zero, ENNReal.toReal_zero, max_self]
      · simp_rw [mul_comm _ ((∂ν/∂_ ∘ₘ _) _).toReal, ← smul_eq_mul]
        rw [setIntegral_rnDeriv_smul hνac hs.compl]
    _ = ∫ x, (π {false} * (∂(μ.singularPart ν)/∂Kernel.boolKernel μ ν ∘ₘ π) x).toReal
          ∂Kernel.boolKernel μ ν ∘ₘ π
        + ∫ x in sᶜ, (max 0 ((π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal)) ∂ν := by
      simp_rw [max_eq_right ENNReal.toReal_nonneg]
      congr 1
      apply setIntegral_congr_ae hs.compl
      filter_upwards [μ.rnDeriv_restrict ν hs.compl] with x hx1 hxs
      rw [hx1, indicator_of_mem hxs]
    _ = ∫ x, (max 0 ((π {false} * (∂μ/∂ν) x).toReal - (π {true}).toReal)) ∂ν
        + (π {false} * (μ.singularPart ν) univ).toReal := by
      simp_rw [ENNReal.toReal_mul, add_comm (∫ _, _ ∂_ ∘ₘ _)]
      rw [integral_const_mul, Measure.integral_toReal_rnDeriv
        ((μ.singularPart_le ν).absolutelyContinuous.trans hμac), measureReal_def]
      nth_rw 2 [← integral_add_compl hs]
      swap
      · exact (integrable_zero _ _ _).sup
          ((Measure.integrable_toReal_rnDeriv.const_mul _).sub (integrable_const _))
      rw [setIntegral_measure_zero _ (μ.measure_singularPartSet ν), zero_add]

/-- Integral form of the statistical information, when `π {true} * ν univ ≤ π {false} * μ univ`.
It follows from `toReal_statInfo_eq_integral_max_of_le` applied to `ν`, `μ` and the swapped prior,
through the Lebesgue decomposition of `ν` with respect to `μ`. -/
lemma toReal_statInfo_eq_integral_max_of_ge [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure π] (h : π {true} * ν univ ≤ π {false} * μ univ) :
    (statInfo μ ν π).toReal
      = ∫ x, max 0 ((π {true}).toReal - (π {false} * (∂μ/∂ν) x).toReal) ∂ν := by
  have h_false : π.map Bool.not {false} = π {true} := by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    simp [Set.preimage]
  have h_true : π.map Bool.not {true} = π {false} := by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    simp [Set.preimage]
  rw [statInfo_symm, toReal_statInfo_eq_integral_max_of_le (by rwa [h_false, h_true]), h_false,
    h_true]
  set t := π {true}
  set f := π {false}
  have ht : t ≠ ∞ := measure_ne_top _ _
  have hf : f ≠ ∞ := measure_ne_top _ _
  have h_meas_left : Measurable fun x ↦ t * (∂ν/∂μ) x - f :=
    ((ν.measurable_rnDeriv μ).const_mul _).sub measurable_const
  have h_meas_right : Measurable fun x ↦ t - f * (∂μ/∂ν) x :=
    measurable_const.sub ((μ.measurable_rnDeriv ν).const_mul _)
  -- both integrals are integrals of truncated differences in `ℝ≥0∞`
  have h_left : ∫ x, max 0 ((t * (∂ν/∂μ) x).toReal - f.toReal) ∂μ
      = (∫⁻ x, t * (∂ν/∂μ) x - f ∂μ).toReal := by
    rw [← integral_toReal h_meas_left.aemeasurable]
    · refine integral_congr_ae ?_
      filter_upwards [ν.rnDeriv_ne_top μ] with x hx
      rw [ENNReal.toReal_sub_eq_max_zero (by finiteness) hf]
    · filter_upwards [ν.rnDeriv_ne_top μ] with x hx
      exact tsub_le_self.trans_lt (by finiteness)
  have h_right : ∫ x, max 0 (t.toReal - (f * (∂μ/∂ν) x).toReal) ∂ν
      = (∫⁻ x, t - f * (∂μ/∂ν) x ∂ν).toReal := by
    rw [← integral_toReal h_meas_right.aemeasurable]
    · refine integral_congr_ae ?_
      filter_upwards [μ.rnDeriv_ne_top ν] with x hx
      rw [ENNReal.toReal_sub_eq_max_zero ht (by finiteness)]
    · exact ae_of_all _ fun _ ↦ tsub_le_self.trans_lt ht.lt_top
  -- decomposition of `ν` with respect to `μ`: `∂μ/∂ν = 0` on the singular part, and
  -- `∂μ/∂ν = (∂ν/∂μ)⁻¹` on the absolutely continuous part
  have h_key : ∫⁻ x, t - f * (∂μ/∂ν) x ∂ν
      = ∫⁻ x, t * (∂ν/∂μ) x - f ∂μ + t * ν.singularPart μ univ := by
    rw [lintegral_eq_add_singularPart_withDensity μ ν h_meas_right, add_comm]
    congr 1
    · refine lintegral_congr_ae ?_
      filter_upwards [Measure.rnDeriv_eq_inv_rnDeriv_of_ne_zero ν μ, ν.rnDeriv_ne_top μ]
        with x hx hx_top
      by_cases h0 : (∂ν/∂μ) x = 0
      · simp [h0]
      rw [hx h0, ENNReal.mul_sub (fun _ _ ↦ hx_top), mul_comm ((∂ν/∂μ) x) t, mul_left_comm,
        ENNReal.mul_inv_cancel h0 hx_top, mul_one]
    · rw [← lintegral_const]
      refine lintegral_congr_ae ?_
      filter_upwards [Measure.rnDeriv_eq_zero_ae_singularPart μ ν] with x hx
      simp [hx]
  have h_fin : ∫⁻ x, t * (∂ν/∂μ) x - f ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun _ ↦ tsub_le_self)
    rw [lintegral_const_mul _ (ν.measurable_rnDeriv μ)]
    exact ENNReal.mul_ne_top ht (Measure.lintegral_rnDeriv_lt_top ν μ).ne
  rw [h_left, h_right, h_key, ENNReal.toReal_add h_fin (by finiteness)]

lemma toReal_statInfo_eq_integral_abs (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {π : Measure Bool} [IsFiniteMeasure π] :
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
      integral_const_mul, abs_neg, neg_sub]
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
        · simp_rw [ENNReal.toReal_mul, integral_const_mul, Measure.integral_toReal_rnDeriv',
          measureReal_def, mul_sub]
        · rw [integral_const, smul_eq_mul, measureReal_def, ENNReal.toReal_mul, mul_comm]
      _ = _ := by ring
  · rw [abs_of_nonneg]
    swap
    · refine sub_nonneg.mpr <| (ENNReal.toReal_le_toReal ?_ ?_).mpr h
        <;> try simp only [ne_eq, measure_ne_top _ _, not_false_eq_true, ENNReal.mul_ne_top]
    simp_rw [toReal_statInfo_eq_integral_max_of_ge h, max_eq_add_add_abs_sub, zero_add, zero_sub,
      integral_const_mul, abs_neg, neg_sub]
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
        simp_rw [ENNReal.toReal_mul, integral_const_mul, Measure.integral_toReal_rnDeriv',
          measureReal_def, mul_sub]
        rw [integral_const, smul_eq_mul, measureReal_def, ← sub_add, mul_comm (ν univ).toReal]
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

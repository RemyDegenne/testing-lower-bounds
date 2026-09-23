/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import TestingLowerBounds.ForMathlib.MaxMinEqAbs
public import TestingLowerBounds.Testing.BoolMeasure
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.Probability.Decision.BayesEstimator
public import Mathlib.Probability.Decision.Risk.Basic
public import Mathlib.Probability.Decision.Risk.RiskIncrease

/-!
# Simple Bayesian binary hypothesis testing

## Main definitions

* `simpleBinaryLoss`: the 0-1 loss on `Bool`, `ℓ(y, z) = 𝕀{y ≠ z}`.
* `bayesBinaryRisk μ ν π`: the Bayes risk of the simple binary hypothesis testing problem between
  `μ` and `ν` with respect to the prior `π`.

## Main statements

* `bayesBinaryRisk_le_bayesBinaryRisk_comp`: data-processing inequality.
* `bayesBinaryRisk_eq_lintegral_min`: formula for the Bayes binary risk as an integral.

-/

@[expose] public section

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞}

section SimpleBinaryHypTest

/-- The loss of the simple binary hypothesis testing problem: `ℓ(y, z) = 𝕀{y ≠ z}`. -/
noncomputable
def simpleBinaryLoss (y z : Bool) : ℝ≥0∞ := if y = z then 0 else 1

@[simp] lemma simpleBinaryLoss_self (y : Bool) : simpleBinaryLoss y y = 0 := by
  simp [simpleBinaryLoss]

@[simp] lemma simpleBinaryLoss_true_false : simpleBinaryLoss true false = 1 := by
  simp [simpleBinaryLoss]

@[simp] lemma simpleBinaryLoss_false_true : simpleBinaryLoss false true = 1 := by
  simp [simpleBinaryLoss]

lemma measurable_simpleBinaryLoss : Measurable (Function.uncurry simpleBinaryLoss) :=
  .of_discrete

@[simp]
lemma lintegral_simpleBinaryLoss_true (ξ : Measure Bool) :
    ∫⁻ z, simpleBinaryLoss true z ∂ξ = ξ {false} := by
  simp [lintegral_fintype, simpleBinaryLoss]

@[simp]
lemma lintegral_simpleBinaryLoss_false (ξ : Measure Bool) :
    ∫⁻ z, simpleBinaryLoss false z ∂ξ = ξ {true} := by
  simp [lintegral_fintype, simpleBinaryLoss]

/-- The function `x ↦ 𝕀{π₀ * ∂μ/∂(boolKernel μ ν ∘ₘ π) x ≤ π₁ * ∂ν/∂(boolKernel μ ν ∘ₘ π) x}`.
It is an argmin estimator for the simple binary hypothesis testing problem. -/
noncomputable
def binaryGenBayesEstimator (μ ν : Measure 𝒳) (π : Measure Bool) : 𝒳 → Bool :=
  let E : Set 𝒳 := {x | π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x
    ≤ π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x}
  fun x ↦ Bool.ofNat (E.indicator 1 x)

lemma isArgminEstimator_binaryGenBayesEstimator (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    IsArgminEstimator simpleBinaryLoss (Kernel.boolKernel μ ν) π
      (binaryGenBayesEstimator μ ν π) := by
  refine ⟨?_, ?_⟩
  · simp_rw [binaryGenBayesEstimator]
    refine Measurable.of_discrete.fun_comp (measurable_one.indicator (measurableSet_le ?_ ?_))
      <;> fun_prop
  · filter_upwards [posterior_boolKernel_apply_true μ ν π,
      posterior_boolKernel_apply_false μ ν π] with x h_true h_false
    refine le_antisymm (le_iInf fun b ↦ ?_) (iInf_le _ _)
    cases b <;> by_cases
      π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x
        ≤ π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x
      <;> simp_all [Bool.lintegral_bool, binaryGenBayesEstimator, Bool.ofNat, simpleBinaryLoss,
        -not_le, le_of_not_ge]

lemma hasArgminEstimator_simpleBinaryLoss (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    HasArgminEstimator simpleBinaryLoss (Kernel.boolKernel μ ν) π :=
  ⟨_, isArgminEstimator_binaryGenBayesEstimator μ ν π⟩

end SimpleBinaryHypTest

/-- The Bayes risk for a prior `π` of an estimation problem with parameter space `Bool` and
data generating kernel `boolKernel μ ν`, when it admits an argmin estimator. -/
lemma bayesRisk_boolKernel_eq_lintegral_iInf {𝒴 : Type*} [MeasurableSpace 𝒴]
    {ℓ : Bool → 𝒴 → ℝ≥0∞} (hℓ : Measurable (Function.uncurry ℓ))
    (μ ν : Measure 𝒳) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] (h : HasArgminEstimator ℓ (Kernel.boolKernel μ ν) π) :
    bayesRisk ℓ (Kernel.boolKernel μ ν) π
      = ∫⁻ x, ⨅ y, π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x * ℓ true y
        + π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x * ℓ false y
        ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  rw [h.bayesRisk_eq hℓ]
  refine lintegral_congr_ae ?_
  filter_upwards [posterior_boolKernel_apply_false μ ν π, posterior_boolKernel_apply_true μ ν π]
    with x h_false h_true
  congr with y
  rw [Bool.lintegral_bool, h_false, h_true]
  ring

/-- The Bayes risk of simple binary hypothesis testing with respect to a prior. -/
noncomputable
def bayesBinaryRisk (μ ν : Measure 𝒳) (π : Measure Bool) : ℝ≥0∞ :=
  bayesRisk simpleBinaryLoss (Kernel.boolKernel μ ν) π

lemma bayesBinaryRisk_eq (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π
      = ⨅ (κ : Kernel 𝒳 Bool) (_ : IsMarkovKernel κ),
        π {true} * (κ ∘ₘ ν) {false} + π {false} * (κ ∘ₘ μ) {true} := by
  rw [bayesBinaryRisk, bayesRisk]
  congr with κ
  congr with _
  simp only [avgRisk, Bool.lintegral_bool, Kernel.comp_boolKernel, Kernel.boolKernel_apply,
    Bool.false_eq_true, ↓reduceIte, simpleBinaryLoss_self, simpleBinaryLoss_true_false,
    simpleBinaryLoss_false_true, zero_mul, one_mul, zero_add, add_zero]
  ring

variable {π : Measure Bool}

/-- `B (a•μ, b•ν; π) = B (μ, ν; (a*π₀, b*π₁)).` -/
lemma bayesBinaryRisk_smul_smul (μ ν : Measure 𝒳) (π : Measure Bool) (a b : ℝ≥0∞) :
    bayesBinaryRisk (a • μ) (b • ν) π
      = bayesBinaryRisk μ ν (π.withDensity (fun x ↦ bif x then b else a)) := by
  simp [bayesBinaryRisk_eq, lintegral_dirac, mul_assoc]

lemma bayesBinaryRisk_eq_bayesBinaryRisk_one_one (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π
      = bayesBinaryRisk (π {false} • μ) (π {true} • ν) (Bool.boolMeasure 1 1) := by
  rw [bayesBinaryRisk_smul_smul, Bool.measure_eq_boolMeasure π, Bool.boolMeasure_withDensity]
  simp

/-- **Data processing inequality** for the Bayes binary risk. -/
lemma bayesBinaryRisk_le_bayesBinaryRisk_comp (μ ν : Measure 𝒳) (π : Measure Bool)
    (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] :
    bayesBinaryRisk μ ν π ≤ bayesBinaryRisk (η ∘ₘ μ) (η ∘ₘ ν) π :=
  (bayesRisk_le_bayesRisk_comp _ _ _ η).trans_eq (by simp [bayesBinaryRisk, Kernel.comp_boolKernel])

@[simp]
lemma bayesBinaryRisk_self (μ : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ μ π = min (π {false}) (π {true}) * μ .univ := by
  rw [bayesBinaryRisk_eq]
  refine le_antisymm ?_ ?_
  · let η : Kernel 𝒳 Bool :=
      if π {true} ≤ π {false} then (Kernel.const 𝒳 (Measure.dirac false))
        else (Kernel.const 𝒳 (Measure.dirac true))
    refine iInf_le_of_le η ?_
    simp_rw [η]
    convert iInf_le _ ?_ using 1
    · split_ifs with h <;> simp [le_of_not_ge, h]
    · split_ifs <;> infer_instance
  · calc
      _ ≥ ⨅ κ, ⨅ (_ : IsMarkovKernel κ), min (π {false}) (π {true}) * (κ ∘ₘ μ) {false}
          + min (π {false}) (π {true}) * (κ ∘ₘ μ) {true} := by
        gcongr <;> simp
      _ = ⨅ κ, ⨅ (_ : IsMarkovKernel κ), min (π {false}) (π {true}) * μ .univ := by
        simp_rw [← mul_add, ← measure_union (show Disjoint {false} {true} from by simp)
          (by trivial), (set_fintype_card_eq_univ_iff ({false} ∪ {true})).mp rfl,
          Measure.comp_apply_univ]
        rfl
      _ = _ := by
        rw [iInf_subtype']
        convert iInf_const
        infer_instance

lemma bayesBinaryRisk_dirac (a b : ℝ≥0∞) (x : 𝒳) (π : Measure Bool) :
    bayesBinaryRisk (a • Measure.dirac x) (b • Measure.dirac x) π
      = min (π {false} * a) (π {true} * b) := by
  rw [bayesBinaryRisk_smul_smul, bayesBinaryRisk_self]
  simp [lintegral_dirac]

lemma bayesBinaryRisk_le_min (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π ≤ min (π {false} * μ .univ) (π {true} * ν .univ) := by
  convert bayesBinaryRisk_le_bayesBinaryRisk_comp μ ν π (Kernel.discard 𝒳)
  rw [Measure.discard_comp, Measure.discard_comp, bayesBinaryRisk_dirac]

@[simp] lemma bayesBinaryRisk_zero_left : bayesBinaryRisk 0 ν π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le

@[simp] lemma bayesBinaryRisk_zero_right : bayesBinaryRisk μ 0 π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le

@[simp] lemma bayesBinaryRisk_zero_prior : bayesBinaryRisk μ ν 0 = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp)) zero_le

lemma bayesBinaryRisk_ne_top (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π ≠ ∞ := by
  refine lt_top_iff_ne_top.mp ((bayesBinaryRisk_le_min μ ν π).trans_lt ?_)
  exact min_lt_iff.mpr <| Or.inl <| ENNReal.mul_lt_top (measure_lt_top π _) (measure_lt_top μ _)

lemma bayesBinaryRisk_of_measure_true_eq_zero (μ ν : Measure 𝒳) (hπ : π {true} = 0) :
    bayesBinaryRisk μ ν π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp [hπ])) zero_le

lemma bayesBinaryRisk_of_measure_false_eq_zero (μ ν : Measure 𝒳) (hπ : π {false} = 0) :
    bayesBinaryRisk μ ν π = 0 :=
  le_antisymm ((bayesBinaryRisk_le_min _ _ _).trans (by simp [hπ])) zero_le

lemma bayesBinaryRisk_symm (μ ν : Measure 𝒳) (π : Measure Bool) :
    bayesBinaryRisk μ ν π = bayesBinaryRisk ν μ (π.map Bool.not) := by
  have : (Bool.not ⁻¹' {true}) = {false} := by ext x; simp
  have h1 : (π.map Bool.not) {true} = π {false} := by
    rw [Measure.map_apply (by exact fun _ a ↦ a) (by trivial), this]
  have : (Bool.not ⁻¹' {false}) = {true} := by ext x; simp
  have h2 : (π.map Bool.not) {false} = π {true} := by
    rw [Measure.map_apply (by exact fun _ a ↦ a) (by trivial), this]
  simp_rw [bayesBinaryRisk_eq, h1, h2, add_comm, iInf_subtype']
  -- from this point on the proof is basically a change of variable inside the iInf,
  -- to do this I define an equivalence between `Subtype IsMarkovKernel` and itself through
  -- the `Bool.not` operation, maybe it can be shortened or something can be separated as
  -- a different lemma, but I'm not sure how useful this would be
  let e : (Kernel 𝒳 Bool) ≃ (Kernel 𝒳 Bool) := by
    have h_id : (Kernel.deterministic Bool.not .of_discrete).comap Bool.not .of_discrete
        = Kernel.id := by
      ext x : 1
      simp_rw [Kernel.comap_apply, Kernel.deterministic_apply, Kernel.id_apply, Bool.not_not]
    refine ⟨fun κ ↦ (Kernel.deterministic Bool.not .of_discrete) ∘ₖ κ,
      fun κ ↦ (Kernel.deterministic Bool.not .of_discrete) ∘ₖ κ, fun κ ↦ ?_, fun κ ↦ ?_⟩ <;>
    · dsimp
      ext x : 1
      rw [← Kernel.comp_assoc, Kernel.comp_deterministic_eq_comap, h_id, Kernel.id_comp]
  let e' : (Subtype (@IsMarkovKernel 𝒳 Bool _ _)) ≃ (Subtype (@IsMarkovKernel 𝒳 Bool _ _)) := by
    refine ⟨fun ⟨κ, _⟩ ↦ ⟨e κ, ?_⟩, fun ⟨κ, _⟩ ↦ ⟨e.symm κ, ?_⟩, fun κ ↦ by simp, fun κ ↦ by simp⟩
      <;> simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, e] <;> infer_instance
  rw [← Equiv.iInf_comp e']
  congr with κ
  simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, e', e]
  have h3 b : Set.indicator {true} (1 : Bool → ℝ≥0∞) b.not = Set.indicator {false} 1 b := by
    cases b <;> simp
  have h4 b : Set.indicator {false} (1 : Bool → ℝ≥0∞) b.not = Set.indicator {true} 1 b := by
    cases b <;> simp
  congr 2 <;>
  · rw [Measure.bind_apply (by trivial) (Kernel.measurable _).aemeasurable,
      Measure.bind_apply (by trivial) (Kernel.measurable _).aemeasurable]
    congr with x
    rw [Kernel.comp_apply']
    simp only [Measure.dirac_apply' _ (show MeasurableSet {true} by trivial),
      Measure.dirac_apply' _ (show MeasurableSet {false} by trivial), Kernel.deterministic_apply]
    swap; trivial
    simp [h3, h4, Bool.lintegral_bool]

lemma avgRisk_binary_of_deterministic_indicator (μ ν : Measure 𝒳) (π : Measure Bool)
    {E : Set 𝒳} (hE : MeasurableSet E) :
    avgRisk simpleBinaryLoss (Kernel.boolKernel μ ν)
      (Kernel.deterministic (fun x ↦ Bool.ofNat (E.indicator 1 x))
        (Measurable.of_discrete.fun_comp (measurable_one.indicator hE))) π
      = π {false} * μ E + π {true} * ν Eᶜ := by
  have h_meas : Measurable fun x ↦ Bool.ofNat (E.indicator 1 x) :=
    Measurable.of_discrete.fun_comp (measurable_one.indicator hE)
  have h1 : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {false} = Eᶜ := by
    ext; simp [Bool.ofNat]
  have h2 : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {true} = E := by
    ext; simp [Bool.ofNat]
  simp only [avgRisk, Bool.lintegral_bool, Kernel.comp_boolKernel, Kernel.boolKernel_apply,
    Bool.false_eq_true, ↓reduceIte, simpleBinaryLoss_self, simpleBinaryLoss_true_false,
    simpleBinaryLoss_false_true, zero_mul, one_mul, zero_add, add_zero,
    Measure.deterministic_comp_eq_map, Measure.map_apply h_meas trivial, h1, h2]
  ring

lemma bayesBinaryRisk_eq_iInf_measurableSet (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = ⨅ E, ⨅ (_ : MeasurableSet E), π {false} * μ E + π {true} * ν Eᶜ := by
  apply le_antisymm
  · simp_rw [le_iInf_iff, bayesBinaryRisk, bayesRisk]
    intro E hE
    rw [← avgRisk_binary_of_deterministic_indicator _ _ _ hE]
    exact iInf_le_of_le _ (iInf_le _ (Kernel.isMarkovKernel_deterministic _))
  · let E := {x | π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) x
      ≤ π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) x}
    have hE : MeasurableSet E := measurableSet_le (by fun_prop) (by fun_prop)
    rw [bayesBinaryRisk, ← (isArgminEstimator_binaryGenBayesEstimator μ ν π).isBayesEstimator
      measurable_simpleBinaryLoss, IsArgminEstimator.kernel]
    simp_rw [binaryGenBayesEstimator]
    rw [avgRisk_binary_of_deterministic_indicator _ _ _ hE]
    exact iInf_le_of_le E (iInf_le _ hE)

lemma bayesBinaryRisk_eq_lintegral_min (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = ∫⁻ x, min (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x)
      (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x) ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  simp_rw [bayesBinaryRisk, bayesRisk_boolKernel_eq_lintegral_iInf measurable_simpleBinaryLoss μ ν π
    (hasArgminEstimator_simpleBinaryLoss μ ν π), iInf_bool_eq]
  simp

lemma toReal_bayesBinaryRisk_eq_integral_min (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    (bayesBinaryRisk μ ν π).toReal
      = ∫ x, min (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
        (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
          ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
  rw [bayesBinaryRisk_eq_lintegral_min, integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · filter_upwards with x; positivity
  · refine Measurable.aestronglyMeasurable <| Measurable.min ?_ ?_
      <;> exact Measure.measurable_rnDeriv _ _ |>.const_mul _ |>.ennreal_toNNReal |>.coe_nnreal_real
  congr 1
  apply lintegral_congr_ae
  filter_upwards [μ.rnDeriv_ne_top _, ν.rnDeriv_ne_top _] with x hxμ hxν
  have : (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x) ≠ ⊤ :=
    (ENNReal.mul_ne_top (measure_ne_top _ _) hxμ)
  have : (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x) ≠ ⊤ :=
    (ENNReal.mul_ne_top (measure_ne_top _ _) hxν)
  rcases le_total (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x)
    (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x) with h | h
  all_goals
  · have h' := (ENNReal.toReal_le_toReal (by assumption) (by assumption)).mpr h
    simp only [h, h', min_eq_left, min_eq_right]
    exact (ENNReal.ofReal_toReal_eq_iff.mpr (by assumption)).symm

lemma toReal_bayesBinaryRisk_eq_integral_abs (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    (bayesBinaryRisk μ ν π).toReal
      = 2⁻¹ * (((Kernel.boolKernel μ ν ∘ₘ π) .univ).toReal
        - ∫ x, |(π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
          - (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal|
            ∂(Kernel.boolKernel μ ν ∘ₘ π)) := by
  simp_rw [toReal_bayesBinaryRisk_eq_integral_min, min_eq_add_sub_abs_sub, integral_const_mul]
  congr
  have hμ_int : Integrable (fun x ↦ (π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal)
      (Kernel.boolKernel μ ν ∘ₘ π) := by
    simp_rw [ENNReal.toReal_mul]
    exact Integrable.const_mul Measure.integrable_toReal_rnDeriv _
  have hν_int : Integrable (fun x ↦ (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal)
      (Kernel.boolKernel μ ν ∘ₘ π) := by
    simp_rw [ENNReal.toReal_mul]
    exact Integrable.const_mul Measure.integrable_toReal_rnDeriv _
  have h_int_abs : Integrable
      (fun x ↦ |(π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal
        - (π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x).toReal|)
      (Kernel.boolKernel μ ν ∘ₘ π) :=
    hμ_int.sub hν_int |>.abs
  rw [integral_sub (by exact hμ_int.add hν_int) h_int_abs, integral_add hμ_int hν_int]
  simp only [ENNReal.toReal_mul, sub_left_inj, integral_const_mul]
  nth_rw 5 [boolKernel_comp_measure]
  calc
    _ = (π {false}).toReal * (μ .univ).toReal + (π {true}).toReal
        * ∫ (a : 𝒳), ((∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) a).toReal ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
      by_cases hπ_false : π {false} = 0
      · simp [hπ_false]
      rw [Measure.integral_toReal_rnDeriv
        (absolutelyContinuous_boolKernel_comp_left μ ν hπ_false)]
      rw [measureReal_def]
    _ = (π {false}).toReal * (μ .univ).toReal + (π {true}).toReal * (ν .univ).toReal := by
      by_cases hπ_true : π {true} = 0
      · simp [hπ_true]
      rw [Measure.integral_toReal_rnDeriv
        (absolutelyContinuous_boolKernel_comp_right μ ν hπ_true)]
      rw [measureReal_def]
    _ = _ := by
      simp_rw [add_comm, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _)
        (measure_ne_top _ _)) (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
        ENNReal.toReal_mul]

lemma bayesBinaryRisk_eq_lintegral_ennnorm (μ ν : Measure 𝒳) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (π : Measure Bool) [IsFiniteMeasure π] :
    bayesBinaryRisk μ ν π = 2⁻¹ * (((Kernel.boolKernel μ ν ∘ₘ π) .univ)
        - ∫⁻ x, ‖(π {false} * (∂μ/∂(Kernel.boolKernel μ ν ∘ₘ π)) x).toReal
          - (π {true} * (∂ν/∂(Kernel.boolKernel μ ν ∘ₘ π)) x).toReal‖₊
            ∂(Kernel.boolKernel μ ν ∘ₘ π)) := by
  rw [← ENNReal.ofReal_toReal (bayesBinaryRisk_ne_top μ ν π),
    toReal_bayesBinaryRisk_eq_integral_abs, ENNReal.ofReal_mul (inv_nonneg.mpr zero_le_two),
    ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat,
    ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_toReal (measure_ne_top _ _),
    ofReal_integral_eq_lintegral_ofReal _ (.of_forall fun _ ↦ by positivity)]
  swap
  · refine ⟨Measurable.aestronglyMeasurable (by fun_prop), ?_⟩
    simp_rw [HasFiniteIntegral, Real.enorm_abs]
    calc
      _ ≤ ∫⁻ a, ‖(π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) a).toReal‖ₑ +
          ‖(π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) a).toReal‖ₑ
            ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
        gcongr
        exact enorm_sub_le
      _ = ∫⁻ a, ‖(π {false} * (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) a).toReal‖ₑ
        ∂(Kernel.boolKernel μ ν ∘ₘ π) +
          ∫⁻ a, ‖(π {true} * (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) a).toReal‖ₑ
            ∂(Kernel.boolKernel μ ν ∘ₘ π) :=
        lintegral_add_left (by fun_prop) _
      _ ≤ π {false} * ∫⁻ a, ‖((∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) a).toReal‖ₑ
        ∂(Kernel.boolKernel μ ν ∘ₘ π) +
          π {true} * ∫⁻ a, ‖((∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) a).toReal‖ₑ
            ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
        simp_rw [ENNReal.toReal_mul, enorm_mul]
        rw [lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
        gcongr <;>
        · rw [Real.enorm_eq_ofReal_abs, ENNReal.abs_toReal]
          exact ENNReal.ofReal_toReal_le
      _ ≤ π {false} * ∫⁻ a, (∂μ/∂Kernel.boolKernel μ ν ∘ₘ π) a ∂(Kernel.boolKernel μ ν ∘ₘ π) +
          π {true} * ∫⁻ a, (∂ν/∂Kernel.boolKernel μ ν ∘ₘ π) a ∂(Kernel.boolKernel μ ν ∘ₘ π) := by
        gcongr <;>
        · rw [Real.enorm_eq_ofReal_abs, ENNReal.abs_toReal]
          exact ENNReal.ofReal_toReal_le
      _ = π {false} * μ .univ + π {true} * ν .univ := by
        congr 1
        · by_cases h_false : π {false} = 0
          · rw [h_false, zero_mul, zero_mul]
          rw [Measure.lintegral_rnDeriv
            (absolutelyContinuous_boolKernel_comp_left μ ν h_false)]
        · by_cases h_true : π {true} = 0
          · rw [h_true, zero_mul, zero_mul]
          rw [Measure.lintegral_rnDeriv
            (absolutelyContinuous_boolKernel_comp_right μ ν h_true)]
      _ < ⊤ :=
        ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _),
          ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)⟩
  simp_rw [← enorm_eq_nnnorm, Real.enorm_eq_ofReal_abs]

end ProbabilityTheory

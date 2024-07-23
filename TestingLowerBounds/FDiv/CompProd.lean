/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.FDiv.Basic
import TestingLowerBounds.FDiv.IntegralRnDerivSingularPart
import Mathlib.Probability.Kernel.Disintegration.Basic
/-!

# f-Divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : ℝ → ℝ}

section Conditional

/--Equivalence between two possible versions of the first condition for the finiteness of the
conditional f divergence, the second version is the preferred one.-/
lemma fDiv_ae_ne_top_iff [IsFiniteKernel κ] [IsFiniteKernel η] :
    (∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    ↔ (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
      ∧ (derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  simp_rw [fDiv_ne_top_iff, eventually_and, eventually_all]

/--Equivalence between two possible versions of the second condition for the finiteness of the
conditional f divergence, the second version is the preferred one.-/
lemma integrable_fDiv_iff [CountableOrCountablyGenerated α β] [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η] (h_int : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (h_ac : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ
      ↔ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ := by
  have h_fin : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤ := fDiv_ae_ne_top_iff.mpr ⟨h_int, h_ac⟩
  by_cases h_top : derivAtTop f = ⊤
  · classical
    simp_rw [fDiv_of_derivAtTop_eq_top h_top]
    simp only [fDiv_ne_top_iff, h_top, forall_true_left] at h_fin
    refine integrable_congr ?_
    filter_upwards [h_fin] with a ha
    rw [if_pos ha, EReal.toReal_coe]
  · have h_fin' := h_fin
    simp_rw [fDiv_ne_top_iff_of_derivAtTop_ne_top h_top] at h_fin
    have : (fun x ↦ (fDiv f (κ x) (η x)).toReal)
        =ᵐ[μ] (fun x ↦ ∫ y, f ((∂κ x/∂η x) y).toReal ∂(η x)
          + (derivAtTop f).toReal * ((κ x).singularPart (η x) Set.univ).toReal) := by
      filter_upwards [h_fin'] with x hx1
      rw [fDiv_of_ne_top hx1, EReal.toReal_add]
      · simp only [EReal.toReal_coe, add_right_inj]
        rw [EReal.toReal_mul]
        simp
      · simp
      · simp
      · simp [h_top, EReal.mul_eq_top, derivAtTop_ne_bot, measure_ne_top]
      · simp [EReal.mul_eq_bot, derivAtTop_ne_bot, h_top, measure_ne_top]
    rw [integrable_congr this]
    have h_int : Integrable (fun x ↦ (derivAtTop f).toReal
        * ((κ x).singularPart (η x) Set.univ).toReal) μ :=
      Integrable.const_mul integrable_singularPart (derivAtTop f).toReal
    have h_eq : (fun x ↦ ∫ y, f ((∂κ x/∂η x) y).toReal ∂η x)
        = (fun x ↦ (∫ y, f ((∂κ x/∂η x) y).toReal ∂η x +
          (derivAtTop f).toReal * ((κ x).singularPart (η x) Set.univ).toReal)
          - (derivAtTop f).toReal * ((κ x).singularPart (η x) Set.univ).toReal) := by
      ext; simp
    exact ⟨fun h ↦ h_eq ▸ h.sub h_int, fun h ↦ h.add h_int⟩

section CompProd

/-! We show that the integrability of the functions used in `fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η)`
and in `condFDiv f κ η μ` are equivalent. -/

variable [CountableOrCountablyGenerated α β]

lemma fDiv_compProd_ne_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ⊤ ↔
      (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a)) ν
        ∧ (derivAtTop f = ⊤ → μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [fDiv_ne_top_iff, integrable_f_rnDeriv_compProd_iff hf h_cvx,
    Kernel.Measure.absolutelyContinuous_compProd_iff, and_assoc]

lemma fDiv_compProd_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) = ⊤ ↔
      (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a)) →
        Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂η a) ν →
        derivAtTop f = ⊤ ∧ (μ ≪ ν → ¬∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_ne_top_iff hf h_cvx]
  push_neg
  rfl

lemma fDiv_compProd_right_ne_top_iff [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ⊤ ↔
      (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a)) μ
        ∧ (derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [fDiv_compProd_ne_top_iff hf h_cvx]
  have h_self := μ.rnDeriv_self
  refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun h ↦ ⟨?_, ?_, ?_⟩⟩
  · filter_upwards [h_self, h.1] with a ha1 ha2
    simp_rw [ha1, one_mul] at ha2
    exact ha2
  · refine (integrable_congr ?_).mp h.2.1
    filter_upwards [h_self] with a ha1
    simp_rw [ha1, one_mul]
  · simp only [Measure.AbsolutelyContinuous.rfl, true_and] at h
    exact h.2.2
  · filter_upwards [h_self, h.1] with a ha1 ha2
    simp_rw [ha1, one_mul]
    exact ha2
  · refine (integrable_congr ?_).mp h.2.1
    filter_upwards [h_self] with a ha1
    simp_rw [ha1, one_mul]
  · simp only [Measure.AbsolutelyContinuous.rfl, true_and]
    exact h.2.2

lemma fDiv_compProd_right_eq_top_iff [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = ⊤ ↔
      (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a)) →
        Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ →
        derivAtTop f = ⊤ ∧ ¬∀ᵐ a ∂μ, κ a ≪ η a := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_right_ne_top_iff hf h_cvx]
  push_neg
  rfl

lemma fDiv_compProd_left_ne_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) ≠ ⊤ ↔
      Integrable (fun a ↦ f ((∂μ/∂ν) a).toReal) ν ∧ (derivAtTop f = ⊤ → μ ≪ ν) := by
  rw [fDiv_compProd_ne_top_iff hf h_cvx]
  have h_one : ∀ a, ∂(κ a)/∂(κ a) =ᵐ[κ a] 1 := fun a ↦ Measure.rnDeriv_self (κ a)
  simp only [ENNReal.toReal_mul, Measure.AbsolutelyContinuous.rfl, eventually_true, and_true]
  have : ∀ a, ∫ b, f (((∂μ/∂ν) a).toReal * ((∂κ a/∂κ a) b).toReal) ∂κ a
        = ∫ _, f (((∂μ/∂ν) a).toReal) ∂κ a := by
      refine fun a ↦ integral_congr_ae ?_
      filter_upwards [h_one a] with b hb
      simp [hb]
  refine ⟨fun ⟨_, h2, h3⟩ ↦ ⟨?_, h3⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, ?_, h2⟩⟩
  · refine (integrable_congr ?_).mpr h2
    refine ae_of_all _ (fun a ↦ ?_)
    simp [this]
  · refine ae_of_all _ (fun a ↦ ?_)
    have : (fun x ↦ f (((∂μ/∂ν) a).toReal * ((∂κ a/∂κ a) x).toReal))
        =ᵐ[κ a] (fun _ ↦ f ((∂μ/∂ν) a).toReal) := by
      filter_upwards [h_one a] with b hb
      simp [hb]
    rw [integrable_congr this]
    exact integrable_const _
  · simpa only [this, integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]

lemma fDiv_compProd_left_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = ⊤ ↔
      Integrable (fun a ↦ f ((∂μ/∂ν) a).toReal) ν → (derivAtTop f = ⊤ ∧ ¬ μ ≪ ν) := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_left_ne_top_iff hf h_cvx]
  push_neg
  rfl

lemma fDiv_compProd_right [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = fDiv f μ ν := by
  by_cases h_top : fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = ⊤
  · symm
    rw [h_top, fDiv_eq_top_iff]
    have h_top' := (fDiv_compProd_left_eq_top_iff hf h_cvx).mp h_top
    by_cases h : Integrable (fun a ↦ f ((∂μ/∂ν) a).toReal) ν
    · exact Or.inr (h_top' h)
    · exact Or.inl h
  · have h_top' := (fDiv_compProd_left_ne_top_iff hf h_cvx).mp h_top
    have h_top'' : fDiv f μ ν ≠ ⊤ := by rwa [fDiv_ne_top_iff]
    rw [fDiv_of_ne_top h_top, fDiv_of_ne_top h_top'']
    have h := integral_f_compProd_left_congr μ ν κ (f := f)
    simp only [measure_univ, ENNReal.one_toReal, one_mul] at h
    rw [integral_congr_ae h.symm, Measure.integral_compProd]
    · congr
      rw [singularPart_compProd_left, Measure.compProd_apply MeasurableSet.univ]
      simp
    · rw [← ne_eq, fDiv_ne_top_iff] at h_top
      exact h_top.1

variable {γ : Type*} [MeasurableSpace γ]

lemma fDiv_toReal_eq_ae {ξ : Kernel α β} {κ η : Kernel (α × β) γ} [IsFiniteKernel κ]
    (h_ac : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, κ (a, b) ≪ η (a, b))
    (h_int : ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a,
      Integrable (fun x ↦ f ((∂κ (a, b)/∂η (a, b)) x).toReal) (η (a, b))) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, (fDiv f (κ (a, b)) (η (a, b))).toReal =
      ∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)
      + (derivAtTop f).toReal * (((κ (a, b)).singularPart (η (a, b)) Set.univ)).toReal := by
  filter_upwards [eventually_all.mpr h_ac, h_int] with a ha_ae ha_int
  filter_upwards [eventually_all.mpr ha_ae, ha_int] with b hb_ae hb_int
  rw [← EReal.toReal_coe (∫ _, _ ∂_), fDiv_of_integrable hb_int, ← EReal.toReal_coe_ennreal,
    ← EReal.toReal_mul]
  refine EReal.toReal_add ?_ ?_ ?_ ?_
  · simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true]
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
  all_goals
  · by_cases h_deriv : derivAtTop f = ⊤
    · simp [Measure.singularPart_eq_zero_of_ac <| hb_ae h_deriv]
    · simp only [ne_eq, EReal.mul_eq_top, EReal.mul_eq_bot, derivAtTop_ne_bot, false_and,
        EReal.coe_ennreal_ne_bot, and_false, h_deriv, EReal.coe_ennreal_pos,
        Measure.measure_univ_pos, ne_eq, EReal.coe_ennreal_eq_top_iff, false_or, not_and]
      exact fun _ ↦ measure_ne_top _ _

end CompProd

end Conditional

lemma f_rnDeriv_ae_le_integral [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    (fun a ↦ f ((∂μ/∂ν) a * κ a Set.univ).toReal)
      ≤ᵐ[ν] fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a) := by
  have h_compProd := Kernel.rnDeriv_measure_compProd' μ ν κ η
  have h_lt_top := Measure.ae_ae_of_ae_compProd <| Measure.rnDeriv_lt_top (μ ⊗ₘ κ) (ν ⊗ₘ η)
  have := Measure.integrable_toReal_rnDeriv (μ := μ ⊗ₘ κ) (ν := ν ⊗ₘ η)
  rw [Measure.integrable_compProd_iff] at this
  swap
  · refine (Measurable.stronglyMeasurable ?_).aestronglyMeasurable
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hκη' : ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → κ a ≪ η a := Measure.ae_rnDeriv_ne_zero_imp_of_ae hκη
  filter_upwards [hκη', h_compProd, h_lt_top, h_int.compProd_mk_left_ae', this.1]
    with a h_ac h_eq h_lt_top h_int' h_rnDeriv_int
  calc f ((∂μ/∂ν) a * κ a Set.univ).toReal
    = f ((∂μ/∂ν) a * ∫⁻ b, (∂κ a/∂η a) b ∂η a).toReal := by
        by_cases h0 : (∂μ/∂ν) a = 0
        · simp [h0]
        · rw [Measure.lintegral_rnDeriv (h_ac h0)]
  _ = f (∫⁻ b,(∂μ/∂ν) a * (∂κ a/∂η a) b ∂η a).toReal := by
        rw [lintegral_const_mul _ (Measure.measurable_rnDeriv _ _)]
  _ = f (∫⁻ b, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b) ∂η a).toReal := by rw [lintegral_congr_ae h_eq]
  _ = f (∫ b, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a) := by
        rw [integral_toReal _ h_lt_top]
        exact ((Measure.measurable_rnDeriv _ _).comp measurable_prod_mk_left).aemeasurable
  _ ≤ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a := by
        rw [← average_eq_integral, ← average_eq_integral]
        exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp) h_rnDeriv_int h_int'

lemma integrable_f_rnDeriv_mul_kernel [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun a ↦ f ((∂μ/∂ν) a * κ a Set.univ).toReal) ν := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun a ↦ f ((∂μ/∂ν) a * κ a Set.univ).toReal)
    (g₁ := fun x ↦ c * ((∂μ/∂ν) x * κ x Set.univ).toReal + c')
    (g₂ := fun x ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (x, b)).toReal ∂(η x))
    ?_ ?_ ?_ ?_ ?_
  · exact (hf.comp_measurable ((Measure.measurable_rnDeriv _ _).mul
      (Kernel.measurable_coe _ MeasurableSet.univ)).ennreal_toReal).aestronglyMeasurable
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_ae_le_integral μ ν κ η hf_cvx hf_cont h_int hκη
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    simp_rw [ENNReal.toReal_mul]
    have h := integrable_rnDeriv_mul_withDensity μ ν κ η
    have h_ae : ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → Kernel.withDensity η (Kernel.rnDeriv κ η) a = κ a := by
      refine Measure.ae_rnDeriv_ne_zero_imp_of_ae ?_
      filter_upwards [hκη] with x hx
      rw [Kernel.withDensity_rnDeriv_eq hx]
    refine (integrable_congr ?_).mp h
    filter_upwards [h_ae] with x hx
    by_cases h0 : (∂μ/∂ν) x = 0
    · simp [h0]
    · rw [hx h0]
  · exact h_int.integral_compProd'

lemma integrable_f_rnDeriv_mul_withDensity [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η)) :
    Integrable (fun a ↦
      f ((∂μ/∂ν) a * Kernel.withDensity η (Kernel.rnDeriv κ η) a Set.univ).toReal) ν := by
  refine integrable_f_rnDeriv_mul_kernel μ ν _ η hf hf_cvx hf_cont ?_ ?_
  · refine (integrable_congr ?_).mp h_int
    filter_upwards [Measure.rnDeriv_measure_compProd_Kernel_withDensity μ ν κ η] with x hx
    rw [hx]
  · exact ae_of_all _ (fun _ ↦ Kernel.withDensity_absolutelyContinuous _ _)

lemma integral_f_rnDeriv_mul_le_integral [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫ x, f ((∂μ/∂ν) x * κ x Set.univ).toReal ∂ν
      ≤ ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η) := by
  rw [Measure.integral_compProd h_int]
  refine integral_mono_ae ?_ ?_ ?_
  · exact integrable_f_rnDeriv_mul_kernel μ ν κ η hf hf_cvx hf_cont h_int hκη
  · rw [integrable_f_rnDeriv_compProd_iff hf hf_cvx] at h_int
    rw [integrable_congr (integral_f_compProd_congr _ _ _ _)]
    exact h_int.2
  · exact f_rnDeriv_ae_le_integral μ ν κ η hf_cvx hf_cont h_int hκη

lemma integral_f_rnDeriv_mul_withDensity_le_integral [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η)) :
    ∫ x, f ((∂μ/∂ν) x * Kernel.withDensity η (Kernel.rnDeriv κ η) x Set.univ).toReal ∂ν
      ≤ ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η) := by
  calc ∫ x, f ((∂μ/∂ν) x * Kernel.withDensity η (Kernel.rnDeriv κ η) x Set.univ).toReal ∂ν
    ≤ ∫ x, f ((∂μ ⊗ₘ (Kernel.withDensity η (Kernel.rnDeriv κ η))/∂ν ⊗ₘ η) x).toReal
      ∂(ν ⊗ₘ η) := by
        refine integral_f_rnDeriv_mul_le_integral μ ν (Kernel.withDensity η (Kernel.rnDeriv κ η))
          η hf hf_cvx hf_cont ?_ ?_
        · refine (integrable_congr ?_).mpr h_int
          filter_upwards [Measure.rnDeriv_measure_compProd_Kernel_withDensity μ ν κ η] with x hx
          rw [hx]
        · exact ae_of_all _ (fun _ ↦ Kernel.withDensity_absolutelyContinuous _ _)
  _ = ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η) := by
        refine integral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_measure_compProd_Kernel_withDensity μ ν κ η] with x hx
        rw [hx]

lemma f_rnDeriv_le_add [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsFiniteKernel η]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (h_deriv : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∀ᵐ a ∂ ν, f ((∂μ/∂ν) a).toReal
      ≤ f ((∂μ/∂ν) a * Kernel.withDensity η (Kernel.rnDeriv κ η) a Set.univ).toReal
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal
          * (Kernel.singularPart κ η a Set.univ).toReal := by
  by_cases h_deriv_top : derivAtTop f = ⊤
  · simp only [ENNReal.toReal_mul, h_deriv_top, EReal.toReal_top, zero_mul, add_zero]
    have h_ae : ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → Kernel.withDensity η (Kernel.rnDeriv κ η) a = κ a := by
      refine Measure.ae_rnDeriv_ne_zero_imp_of_ae ?_
      filter_upwards [h_deriv h_deriv_top] with a ha_ac
      rw [Kernel.withDensity_rnDeriv_eq ha_ac]
    filter_upwards [h_ae] with a ha
    by_cases h0 : (∂μ/∂ν) a = 0
    · simp [h0]
    · rw [ha h0]
      simp
  refine ae_of_all _ (fun a ↦ ?_)
  simp only [ENNReal.toReal_mul]
  let κ' := Kernel.withDensity η (Kernel.rnDeriv κ η)
  calc f ((∂μ/∂ν) a).toReal
  _ ≤ f (((∂μ/∂ν) a).toReal * (κ' a Set.univ).toReal)
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal * (1 - (κ' a Set.univ).toReal) := by
      refine le_add_derivAtTop' hf_cvx h_deriv_top ENNReal.toReal_nonneg ENNReal.toReal_nonneg ?_
      calc (κ' a Set.univ).toReal
      _ ≤ (κ a Set.univ).toReal := by
          gcongr
          · exact measure_ne_top _ _
          · exact Kernel.withDensity_rnDeriv_le κ η a Set.univ
      _ = 1 := by simp
  _ = f (((∂μ/∂ν) a).toReal * (κ' a Set.univ).toReal)
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal
          * (Kernel.singularPart κ η a Set.univ).toReal := by
      congr
      norm_cast
      unfold_let κ'
      rw [sub_eq_iff_eq_add, ← ENNReal.one_toReal, ← measure_univ (μ := κ a)]
      conv_lhs => rw [← Kernel.rnDeriv_add_singularPart κ η, add_comm]
      simp only [Kernel.coe_add, Pi.add_apply, Measure.coe_add]
      rw [ENNReal.toReal_add]
      · exact measure_ne_top _ _
      · exact measure_ne_top _ _

lemma integrable_f_rnDeriv_of_integrable_compProd' [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (h_deriv : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun a ↦ f ((∂μ/∂ν) a).toReal)
    (g₁ := fun a ↦ c * ((∂μ/∂ν) a).toReal + c')
    (g₂ := fun a ↦ f ((∂μ/∂ν) a * Kernel.withDensity η (Kernel.rnDeriv κ η) a Set.univ).toReal
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal
          * (Kernel.singularPart κ η a Set.univ).toReal)
    ?_ ?_ ?_ ?_ ?_
  · exact (hf.comp_measurable (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_le_add μ ν κ η hf_cvx h_deriv
  · exact (Measure.integrable_toReal_rnDeriv.const_mul _).add (integrable_const _)
  · refine Integrable.add ?_ ?_
    · exact integrable_f_rnDeriv_mul_withDensity μ ν κ η hf hf_cvx hf_cont hf_int
    · simp_rw [mul_assoc]
      refine Integrable.const_mul ?_ _
      simp_rw [Kernel.singularPart_eq_singularPart_measure]
      exact integrable_rnDeriv_mul_singularPart _ _ _ _

lemma fDiv_ne_top_of_fDiv_compProd_ne_top [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_ne_top : fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ⊤) :
    fDiv f μ ν ≠ ⊤ := by
  rw [fDiv_ne_top_iff]
  have h_ne_top' := (fDiv_compProd_ne_top_iff hf hf_cvx).mp h_ne_top
  obtain ⟨h1, h2, h3⟩ := h_ne_top'
  refine ⟨?_, fun h_top ↦ (h3 h_top).1⟩
  rw [fDiv_ne_top_iff] at h_ne_top
  exact integrable_f_rnDeriv_of_integrable_compProd' μ ν κ η hf hf_cvx hf_cont h_ne_top.1
    (fun h ↦ (h3 h).2)

lemma integral_f_rnDeriv_le_integral_add [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (h_deriv : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫ x, f ((∂μ/∂ν) x).toReal ∂ν
      ≤ ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η)
      + (derivAtTop f).toReal
        * ∫ a, ((∂μ/∂ν) a).toReal * (Kernel.singularPart κ η a Set.univ).toReal ∂ν := by
  suffices ∫ x, f ((∂μ/∂ν) x).toReal ∂ν
      ≤ ∫ x, f ((∂μ/∂ν) x * Kernel.withDensity η (Kernel.rnDeriv κ η) x Set.univ).toReal ∂ν
      + (derivAtTop f).toReal
        * ∫ a, ((∂μ/∂ν) a).toReal * (Kernel.singularPart κ η a Set.univ).toReal ∂ν by
    refine this.trans ?_
    gcongr
    exact integral_f_rnDeriv_mul_withDensity_le_integral μ ν κ η hf hf_cvx hf_cont h_int
  let κ' := Kernel.withDensity η (Kernel.rnDeriv κ η)
  have h : ∀ᵐ a ∂ν, f ((∂μ/∂ν) a).toReal
      ≤ f ((∂μ/∂ν) a * κ' a Set.univ).toReal
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal
          * (Kernel.singularPart κ η a Set.univ).toReal :=
    f_rnDeriv_le_add _ _ _ _ hf_cvx h_deriv
  have h_int_mul : Integrable (fun a ↦ f ((∂μ/∂ν) a * κ' a Set.univ).toReal) ν :=
    integrable_f_rnDeriv_mul_withDensity μ ν κ η hf hf_cvx hf_cont h_int
  have h_int_right : Integrable (fun a ↦ (derivAtTop f).toReal
      * ((∂μ/∂ν) a).toReal * (Kernel.singularPart κ η a Set.univ).toReal) ν := by
    simp_rw [mul_assoc]
    refine Integrable.const_mul ?_ _
    simp_rw [Kernel.singularPart_eq_singularPart_measure]
    exact integrable_rnDeriv_mul_singularPart _ _ _ _
  refine (integral_mono_ae ?_ ?_ h).trans_eq ?_
  · exact integrable_f_rnDeriv_of_integrable_compProd' μ ν κ η hf hf_cvx hf_cont h_int h_deriv
  · exact h_int_mul.add h_int_right
  rw [integral_add h_int_mul h_int_right]
  unfold_let κ'
  simp_rw [mul_assoc]
  rw [integral_mul_left]

lemma le_fDiv_compProd [CountableOrCountablyGenerated α β] (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Set.Ici 0) f)
    (hf_cont : ContinuousOn f (Set.Ici 0)) :
    fDiv f μ ν ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  by_cases h_top : fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) = ⊤
  · simp [h_top]
  rw [fDiv_of_ne_top (fDiv_ne_top_of_fDiv_compProd_ne_top μ ν κ η hf hf_cvx hf_cont h_top),
    fDiv_of_ne_top h_top]
  obtain h_int := (fDiv_ne_top_iff.mp h_top).1
  rw [← ne_eq, fDiv_compProd_ne_top_iff hf hf_cvx] at h_top
  obtain ⟨_, _, h3⟩ := h_top
  calc ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * Measure.singularPart μ ν Set.univ
    ≤ ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η)
      + (derivAtTop f).toReal
        * ∫ a, ((∂μ/∂ν) a).toReal * (Kernel.singularPart κ η a Set.univ).toReal ∂ν
      + derivAtTop f * Measure.singularPart μ ν Set.univ := by
        gcongr
        norm_cast
        exact integral_f_rnDeriv_le_integral_add μ ν κ η hf hf_cvx hf_cont h_int (fun h ↦ (h3 h).2)
  _ = ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η)
      + (derivAtTop f).toReal
        * (((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) Set.univ).toReal
      + derivAtTop f * Measure.singularPart μ ν Set.univ := by
        simp_rw [Kernel.singularPart_eq_singularPart_measure]
        rw [integral_rnDeriv_mul_singularPart _ _ _ _ MeasurableSet.univ, Set.univ_prod_univ]
  _ = ∫ p, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal ∂ν ⊗ₘ η
      + derivAtTop f * (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η) Set.univ := by
        rw [add_assoc]
        congr
        by_cases h_top : derivAtTop f = ⊤
        · simp only [h_top, EReal.toReal_top, EReal.coe_zero, zero_mul, zero_add]
          rw [Measure.singularPart_eq_zero_of_ac (h3 h_top).1,
            Measure.singularPart_eq_zero_of_ac]
          · simp
          · rw [Kernel.Measure.absolutelyContinuous_compProd_iff]
            exact h3 h_top
        lift (derivAtTop f) to ℝ using ⟨h_top, derivAtTop_ne_bot⟩ with df
        simp only [EReal.toReal_coe]
        rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _),
          ← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
        conv_rhs => rw [Measure.haveLebesgueDecomposition_add μ ν]
        rw [Measure.compProd_add_left, add_comm, Measure.singularPart_add]
        simp only [Measure.coe_add, Pi.add_apply]
        rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        simp only [EReal.coe_add]
        norm_cast
        rw [mul_add]
        congr
        rw [singularPart_compProd]
        simp only [Measure.coe_add, Pi.add_apply]
        rw [Measure.compProd_apply MeasurableSet.univ]
        rw [Measure.compProd_apply MeasurableSet.univ]
        simp only [Measure.singularPart_singularPart, Set.preimage_univ]
        rw [← lintegral_add_right]
        · rw [← lintegral_one]
          congr with a
          have h : κ a Set.univ = 1 := by simp
          rw [← Kernel.rnDeriv_add_singularPart κ η] at h
          simp only [Kernel.coe_add, Pi.add_apply, Measure.add_toOuterMeasure,
            OuterMeasure.coe_add] at h
          exact h.symm
        · exact Kernel.measurable_coe _ MeasurableSet.univ

lemma fDiv_fst_le [Nonempty β] [StandardBorelSpace β]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) :
    fDiv f μ.fst ν.fst ≤ fDiv f μ ν := by
  rw [← μ.compProd_fst_condKernel, ← ν.compProd_fst_condKernel, Measure.fst_compProd,
    Measure.fst_compProd]
  exact le_fDiv_compProd μ.fst ν.fst μ.condKernel ν.condKernel hf hf_cvx hf_cont

lemma fDiv_snd_le [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) :
    fDiv f μ.snd ν.snd ≤ fDiv f μ ν := by
  rw [← μ.fst_map_swap, ← ν.fst_map_swap]
  refine (fDiv_fst_le _ _ hf hf_cvx hf_cont).trans_eq ?_
  exact fDiv_map_measurableEmbedding MeasurableEquiv.prodComm.measurableEmbedding

lemma fDiv_comp_le_compProd [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simp_rw [Measure.comp_eq_snd_compProd]
  exact fDiv_snd_le _ _ hf hf_cvx hf_cont

/--The **Data Processing Inequality** for the f-divergence. -/
lemma fDiv_comp_right_le [Nonempty α] [StandardBorelSpace α] [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν := by
  calc fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν)
    ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) := fDiv_comp_le_compProd μ ν κ κ hf hf_cvx hf_cont
  _ = fDiv f μ ν := fDiv_compProd_right μ ν κ hf hf_cvx

end ProbabilityTheory

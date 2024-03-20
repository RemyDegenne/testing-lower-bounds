/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.FDiv

/-!

# f-Divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open Real MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : kernel α β} {f g : ℝ → ℝ}

lemma singularPart_compProd'' [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ kernel.withDensity η (kernel.rnDeriv κ η)
        + μ.singularPart ν ⊗ₘ kernel.singularPart κ η
        + ν.withDensity (∂μ/∂ν) ⊗ₘ kernel.singularPart κ η := by
  conv_lhs => rw [← kernel.rnDeriv_add_singularPart κ η, Measure.compProd_add_right,
    μ.haveLebesgueDecomposition_add ν]
  simp_rw [Measure.compProd_add_left, Measure.singularPart_add]
  have : (ν.withDensity (∂μ/∂ν) ⊗ₘ kernel.withDensity η (kernel.rnDeriv κ η)).singularPart
      (ν ⊗ₘ η) = 0 := by
    refine Measure.singularPart_eq_zero_of_ac (kernel.Measure.absolutelyContinuous_compProd ?_ ?_)
    · exact withDensity_absolutelyContinuous _ _
    · exact ae_of_all _ (kernel.withDensity_absolutelyContinuous _)
  rw [this, add_zero, ← add_assoc]
  congr
  · rw [Measure.singularPart_eq_self]
    exact kernel.Measure.mutuallySingular_compProd_left (Measure.mutuallySingular_singularPart μ ν)
      (kernel.withDensity η (kernel.rnDeriv κ η)) η
  · rw [Measure.singularPart_eq_self]
    exact kernel.Measure.mutuallySingular_compProd_left (Measure.mutuallySingular_singularPart μ ν)
      (kernel.singularPart κ η) η
  · rw [Measure.singularPart_eq_self]
    exact kernel.Measure.mutuallySingular_compProd_right (ν.withDensity (∂μ/∂ν)) ν
      (kernel.mutuallySingular_singularPart _ _)

lemma singularPart_compProd [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ kernel.withDensity η (kernel.rnDeriv κ η)
        + μ ⊗ₘ kernel.singularPart κ η := by
  rw [singularPart_compProd'']
  have : (μ ⊗ₘ kernel.singularPart κ η) = (μ.singularPart ν ⊗ₘ kernel.singularPart κ η)
        + (ν.withDensity (∂μ/∂ν) ⊗ₘ kernel.singularPart κ η) := by
    rw [← Measure.compProd_add_left, ← μ.haveLebesgueDecomposition_add ν]
  rw [this]
  abel_nf
  congr
  trivial

lemma singularPart_compProd' [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η)
      = μ.singularPart ν ⊗ₘ κ + ν.withDensity (∂μ/∂ν) ⊗ₘ kernel.singularPart κ η := by
  rw [singularPart_compProd'']
  have : μ.singularPart ν ⊗ₘ κ
      = μ.singularPart ν ⊗ₘ kernel.withDensity η (kernel.rnDeriv κ η)
        + μ.singularPart ν ⊗ₘ kernel.singularPart κ η := by
    rw [← Measure.compProd_add_right]
    congr
    exact (kernel.rnDeriv_add_singularPart κ η).symm
  rw [this]

lemma singularPart_compProd_left [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : kernel α β) [IsFiniteKernel κ] :
    (μ ⊗ₘ κ).singularPart (ν ⊗ₘ κ) = μ.singularPart ν ⊗ₘ κ := by
  rw [singularPart_compProd', kernel.singularPart_self]
  simp [Measure.singularPart_zero]

lemma singularPart_compProd_right [MeasurableSpace.CountablyGenerated β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) = μ ⊗ₘ kernel.singularPart κ η := by
  rw [singularPart_compProd, Measure.singularPart_self]
  simp [Measure.singularPart_zero]

section Conditional

open Classical in
/- Conditional f-divergence. -/
noncomputable
def condFDiv (f : ℝ → ℝ) (κ η : kernel α β) (μ : Measure α) : EReal :=
  if (∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    ∧ (Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ)
  then ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal)
  else ⊤

lemma condFDiv_of_not_ae_finite (hf : ¬ ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤) :
    condFDiv f κ η μ = ⊤ := by
  rw [condFDiv, if_neg]
  push_neg
  exact fun h ↦ absurd h hf

lemma condFDiv_of_not_integrable
    (hf : ¬ Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) :
    condFDiv f κ η μ = ⊤ := by
  rw [condFDiv, if_neg]
  push_neg
  exact fun _ ↦ hf

lemma condFDiv_eq (hf_ae : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    (hf : Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) :
    condFDiv f κ η μ = ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal) :=
  if_pos ⟨hf_ae, hf⟩

variable [MeasurableSpace.CountablyGenerated β]

section Integrable

/-! We show that the integrability of the functions used in `fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η)`
and in `condFDiv f κ η μ` are equivalent. -/

-- todo find better name
theorem _root_.MeasureTheory.Integrable.compProd_mk_left_ae' [NormedAddCommGroup E]
    [IsFiniteMeasure μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ ⊗ₘ κ)) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ f (x, y)) (κ x) :=
  hf.compProd_mk_left_ae

theorem _root_.MeasureTheory.Integrable.integral_norm_compProd' [NormedAddCommGroup E]
    [IsFiniteMeasure μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun x ↦ ∫ y, ‖f (x, y)‖ ∂(κ x)) μ :=
  hf.integral_norm_compProd

theorem _root_.MeasureTheory.Integrable.integral_compProd' [NormedAddCommGroup E]
    [IsFiniteMeasure μ] [IsSFiniteKernel κ] ⦃f : α × β → E⦄ [NormedSpace ℝ E] [CompleteSpace E]
    (hf : Integrable f (μ ⊗ₘ κ)) :
    Integrable (fun x ↦ ∫ y, f (x, y) ∂(κ x)) μ :=
  hf.integral_compProd

lemma f_compProd_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∀ᵐ a ∂ν, (fun b ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal)
      =ᵐ[η a] fun b ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal := by
  have h_eq_compProd := kernel.rnDeriv_measure_compProd' μ ν κ η
  filter_upwards [h_eq_compProd] with a ha
  filter_upwards [ha] with b hb
  rw [hb]

lemma integral_f_compProd_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a))
      =ᵐ[ν] fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a) := by
  filter_upwards [f_compProd_congr μ ν κ η] with a ha using integral_congr_ae ha

lemma integral_f_compProd_right_congr (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b)).toReal ∂(η a))
      =ᵐ[μ] fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a) := by
  filter_upwards [integral_f_compProd_congr μ μ κ η, Measure.rnDeriv_self μ] with a ha h_eq_one
  rw [ha]
  simp_rw [h_eq_one, one_mul]

lemma integral_f_compProd_left_congr (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : kernel α β) [IsFiniteKernel κ]  :
    (fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ κ) (a, b)).toReal ∂(κ a))
      =ᵐ[ν] fun a ↦ (κ a Set.univ).toReal * f ((∂μ/∂ν) a).toReal := by
  filter_upwards [integral_f_compProd_congr (f := f) μ ν κ κ] with a ha
  have h_one := (κ a).rnDeriv_self
  rw [ha, ← smul_eq_mul,  ← integral_const]
  refine integral_congr_ae ?_
  filter_upwards [h_one] with b hb
  simp [hb]

lemma integrable_f_rnDeriv_of_integrable_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η)) :
    ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((κ a).rnDeriv (η a) x).toReal) (η a) := by
  have h := hf_int.integral_compProd'
  rw [Measure.integrable_compProd_iff] at hf_int
  swap
  · exact (hf.comp_measurable (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
  have h := kernel.rnDeriv_measure_compProd_right' μ κ η
  filter_upwards [h, hf_int.1] with a ha1 ha2
  refine (integrable_congr ?_).mp ha2
  filter_upwards [ha1] with b hb
  rw [hb]

lemma integrable_f_rnDeriv_compProd_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    Integrable (fun x ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η)
      ↔ (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a)) ν := by
  have h_ae_eq : ∀ᵐ a ∂ν, (fun y ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, y)).toReal)
      =ᵐ[η a] fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal := f_compProd_congr μ ν κ η
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
  · have h_int := h.integral_compProd'
    rw [Measure.integrable_compProd_iff] at h
    swap
    · exact (hf.comp_measurable
        (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
    constructor
    · filter_upwards [h.1, h_ae_eq] with a ha1 ha2
      exact (integrable_congr ha2).mp ha1
    · refine (integrable_congr ?_).mp h_int
      filter_upwards [h_ae_eq] with a ha
      exact integral_congr_ae ha
  · rw [Measure.integrable_compProd_iff]
    swap
    · exact (hf.comp_measurable
        (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
    constructor
    · filter_upwards [h1, h_ae_eq] with a ha1 ha2
      exact (integrable_congr ha2).mpr ha1
    · rw [← integrable_congr (integral_f_compProd_congr μ ν κ η)] at h2
      -- todo: cut into two parts, depending on sign of f.
      -- on the positive part, use h2.
      -- on the negative part, use `f x ≥ a * x + b` by convexity, then since both measures are
      -- finite the integral is finite.
      sorry

lemma fDiv_compProd_ne_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ⊤ ↔
      (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a))
        ∧ Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂(η a)) ν
        ∧ (derivAtTop f = ⊤ → μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [fDiv_ne_top_iff, integrable_f_rnDeriv_compProd_iff hf h_cvx,
    kernel.Measure.absolutelyContinuous_compProd_iff, and_assoc]

lemma fDiv_compProd_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) = ⊤ ↔
      (∀ᵐ a ∂ν, Integrable (fun x ↦ f ((∂μ/∂ν) a * (∂κ a/∂η a) x).toReal) (η a)) →
        Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂η a) ν →
        derivAtTop f = ⊤ ∧ (μ ≪ ν → ¬∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_ne_top_iff hf h_cvx]
  push_neg
  rfl

lemma fDiv_compProd_right_ne_top_iff [IsFiniteMeasure μ]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
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
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
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
    simp only
    simp [this]
  · refine ae_of_all _ (fun a ↦ ?_)
    have : (fun x ↦ f (((∂μ/∂ν) a).toReal * ((∂κ a/∂κ a) x).toReal))
        =ᵐ[κ a] (fun _ ↦ f ((∂μ/∂ν) a).toReal) := by
      filter_upwards [h_one a] with b hb
      simp [hb]
    rw [integrable_congr this]
    simp
  · simp only [this, integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
    exact h1

lemma fDiv_compProd_left_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = ⊤ ↔
      Integrable (fun a ↦ f ((∂μ/∂ν) a).toReal) ν → (derivAtTop f = ⊤ ∧ ¬ μ ≪ ν) := by
  rw [← not_iff_not, ← ne_eq, fDiv_compProd_left_ne_top_iff hf h_cvx]
  push_neg
  rfl

lemma integrable_singularPart [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    Integrable (fun x ↦ ((κ x).singularPart (η x) Set.univ).toReal) μ := by
  refine integrable_toReal_of_lintegral_ne_top ?_ (ne_of_lt ?_)
  · simp_rw [← kernel.singularPart_eq_singularPart_measure]
    exact (kernel.measurable_coe _ MeasurableSet.univ).aemeasurable
  calc ∫⁻ x, (κ x).singularPart (η x) Set.univ ∂μ
  _ ≤ ∫⁻ x, κ x Set.univ ∂μ := by
        refine lintegral_mono (fun x ↦ ?_)
        exact Measure.singularPart_le _ _ _
  _ = (μ ⊗ₘ κ) Set.univ := by
        rw [← Set.univ_prod_univ, Measure.compProd_apply_prod MeasurableSet.univ MeasurableSet.univ,
          set_lintegral_univ]
  _ < ⊤ := measure_lt_top _ _

lemma integrable_fDiv_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_fin : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤) :
    Integrable (fun x ↦ EReal.toReal (fDiv f (κ x) (η x))) μ
      ↔ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ := by
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
        * ((κ x).singularPart (η x) Set.univ).toReal) μ := by
      refine Integrable.const_mul ?_ (derivAtTop f).toReal
      exact integrable_singularPart
    refine ⟨fun h ↦ ?_, fun h ↦ h.add h_int⟩
    have : (fun x ↦ ∫ y, f ((∂κ x/∂η x) y).toReal ∂η x)
        = (fun x ↦ (∫ y, f ((∂κ x/∂η x) y).toReal ∂η x +
          (derivAtTop f).toReal * ((κ x).singularPart (η x) Set.univ).toReal)
          - (derivAtTop f).toReal * ((κ x).singularPart (η x) Set.univ).toReal) := by
      ext; simp
    rw [this]
    exact h.sub h_int

lemma condFDiv_ne_top_iff [IsFiniteMeasure μ] [IsMarkovKernel κ] [IsFiniteKernel η] :
  condFDiv f κ η μ ≠ ⊤ ↔
    (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
      ∧ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a)) μ
      ∧ (derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [condFDiv]
  split_ifs with h
  · have h' := h
    simp_rw [fDiv_ne_top_iff] at h
    simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, true_iff]
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [h.1] with a ha
      exact ha.1
    · have h_int := h.2
      rwa [integrable_fDiv_iff h'.1] at h_int
    · intro h_top
      filter_upwards [h.1] with a ha
      exact ha.2 h_top
  · simp only [ne_eq, not_true_eq_false, false_iff, not_and, not_forall, not_eventually,
      exists_prop]
    push_neg at h
    intro hf_int h_int
    simp_rw [fDiv_ne_top_iff] at h
    by_contra h_contra
    simp only [not_and, not_frequently, not_not] at h_contra
    rw [eventually_and] at h
    simp only [hf_int, eventually_all, true_and] at h
    specialize h h_contra
    have h_top : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤ := by
      simp only [ne_eq, fDiv_ne_top_iff, eventually_and, eventually_all]
      exact ⟨hf_int, h_contra⟩
    rw [integrable_fDiv_iff h_top] at h
    exact h h_int

lemma condFDiv_ne_top_iff_fDiv_compProd_ne_top [IsFiniteMeasure μ]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    condFDiv f κ η μ ≠ ⊤ ↔ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ⊤ := by
  rw [condFDiv_ne_top_iff, fDiv_compProd_right_ne_top_iff hf h_cvx]

lemma condFDiv_eq_top_iff_fDiv_compProd_eq_top [IsFiniteMeasure μ]
    [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    condFDiv f κ η μ = ⊤ ↔ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = ⊤ := by
  rw [← not_iff_not]
  exact condFDiv_ne_top_iff_fDiv_compProd_ne_top hf h_cvx

lemma condFDiv_eq_add [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] (hf_ae : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    (hf : Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) :
    condFDiv f κ η μ = (μ[fun a ↦ ∫ y, f ((∂κ a/∂η a) y).toReal ∂η a] : ℝ)
      + (derivAtTop f).toReal * (μ[fun a ↦ ((κ a).singularPart (η a) Set.univ).toReal] : ℝ) := by
  rw [condFDiv_eq hf_ae hf]
  have : (fun x ↦ EReal.toReal (fDiv f (κ x) (η x)))
      =ᵐ[μ] fun x ↦ ∫ y, f ((∂(κ x)/∂(η x)) y).toReal ∂(η x)
        + (derivAtTop f * (κ x).singularPart (η x) Set.univ).toReal := by
    filter_upwards [hf_ae] with x hx
    rw [fDiv_of_ne_top hx, EReal.toReal_add]
    rotate_left
    · simp
    · simp
    · simp only [ne_eq, EReal.mul_eq_top, derivAtTop_ne_bot, false_and, EReal.coe_ennreal_ne_bot,
        and_false, EReal.coe_ennreal_pos, Measure.measure_univ_pos, EReal.coe_ennreal_eq_top_iff,
        measure_ne_top, or_false, false_or, not_and, not_not]
      intro h_top
      rw [fDiv_ne_top_iff] at hx
      simp [h_top, Measure.singularPart_eq_zero_of_ac (hx.2 h_top)]
    · simp only [ne_eq, EReal.mul_eq_bot, derivAtTop_ne_bot, EReal.coe_ennreal_pos,
        Measure.measure_univ_pos, false_and, EReal.coe_ennreal_ne_bot, and_false,
        EReal.coe_ennreal_eq_top_iff, measure_ne_top, or_false, false_or, not_and, not_lt]
      exact fun _ ↦ EReal.coe_ennreal_nonneg _
    rfl
  rw [integral_congr_ae this]
  rw [integral_add]
  rotate_left
  · rwa [integrable_fDiv_iff hf_ae] at hf
  · simp_rw [EReal.toReal_mul]
    convert (integrable_singularPart (κ := κ) (η := η) (μ := μ)).const_mul (derivAtTop f).toReal
    rw [← EReal.coe_ennreal_toReal, EReal.toReal_coe]
    exact measure_ne_top _ _
  simp only [EReal.coe_add, EReal.toReal_mul]
  rw [integral_mul_left]
  simp only [_root_.EReal.toReal_coe_ennreal, EReal.coe_mul]

lemma condFDiv_of_derivAtTop_eq_top [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] (hf_ae : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    (hf : Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) (h_top : derivAtTop f = ⊤) :
    condFDiv f κ η μ = (μ[fun a ↦ ∫ y, f ((∂κ a/∂η a) y).toReal ∂η a] : ℝ) := by
  rw [condFDiv_eq_add hf_ae hf]
  simp [h_top]

end Integrable

lemma fDiv_compProd_left (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = condFDiv f κ η μ := by
  by_cases hf_top : condFDiv f κ η μ = ⊤
  · rwa [hf_top, ← condFDiv_eq_top_iff_fDiv_compProd_eq_top hf h_cvx]
  have hf_top' := hf_top
  have hf_top'' := hf_top
  have hf_top''' := hf_top
  rw [← ne_eq, condFDiv_ne_top_iff] at hf_top'
  rw [condFDiv_eq_top_iff_fDiv_compProd_eq_top hf h_cvx, ← ne_eq, fDiv_ne_top_iff]
    at hf_top''
  rw [condFDiv_eq_top_iff_fDiv_compProd_eq_top hf h_cvx] at hf_top'''
  rcases hf_top' with ⟨h1, h2, h3⟩
  rcases hf_top'' with ⟨h4, h5⟩
  classical
  by_cases h_deriv : derivAtTop f = ⊤
  · rw [fDiv_of_derivAtTop_eq_top h_deriv, if_pos ⟨h4, h5 h_deriv⟩,
      condFDiv_of_derivAtTop_eq_top _ _ h_deriv]
    · sorry
    · sorry
    · sorry
  · rw [fDiv_of_ne_top, condFDiv_eq_add]
    rotate_left
    · sorry
    · sorry
    · exact hf_top'''
    congr
    · sorry
    · rw [EReal.coe_toReal h_deriv derivAtTop_ne_bot]
    · rw [singularPart_compProd_right, Measure.compProd_apply MeasurableSet.univ]
      simp only [Set.preimage_univ]
      rw [integral_toReal]
      rotate_left
      · sorry
      · sorry
      rw [EReal.coe_ennreal_toReal]
      · sorry
      · sorry

end Conditional

lemma fDiv_compProd_right [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : kernel α β) [IsMarkovKernel κ] (hf : StronglyMeasurable f)
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

lemma f_rnDeriv_ae_le_integral [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : ∀ᵐ a ∂ν, κ a ≪ η a) :
    (fun a ↦ f ((∂μ/∂ν) a * κ a Set.univ).toReal)
      ≤ᵐ[ν] fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a) := by
  have h_compProd := kernel.rnDeriv_measure_compProd' μ ν κ η
  have h_lt_top := Measure.ae_ae_of_ae_compProd <| Measure.rnDeriv_lt_top (μ ⊗ₘ κ) (ν ⊗ₘ η)
  have := Measure.integrable_toReal_rnDeriv (μ := μ ⊗ₘ κ) (ν := ν ⊗ₘ η)
  rw [Measure.integrable_compProd_iff] at this
  swap
  · refine (Measurable.stronglyMeasurable ?_).aestronglyMeasurable
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
  filter_upwards [hκη, h_compProd, h_lt_top, h_int.compProd_mk_left_ae', this.1]
    with a h_ac h_eq h_lt_top h_int' h_rnDeriv_int
  calc f ((∂μ/∂ν) a * κ a Set.univ).toReal
    = f ((∂μ/∂ν) a * ∫⁻ b, (∂κ a/∂η a) b ∂η a).toReal := by rw [Measure.lintegral_rnDeriv h_ac]
  _ = f (∫⁻ b,(∂μ/∂ν) a * (∂κ a/∂η a) b ∂η a).toReal := by
        rw [lintegral_const_mul _ (Measure.measurable_rnDeriv _ _)]
  _ = f (∫⁻ b, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b) ∂η a).toReal := by rw [lintegral_congr_ae h_eq]
  _ = f (∫ b, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a) := by
        rw [integral_toReal _ h_lt_top]
        exact ((Measure.measurable_rnDeriv _ _).comp measurable_prod_mk_left).aemeasurable
  _ ≤ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a := by
        rw [← average_eq_integral, ← average_eq_integral]
        exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp) h_rnDeriv_int h_int'

lemma integral_f_rnDeriv_mul_le_integral [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (h_int_int : Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂η a) ν)
    (h_int_meas : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (hκη : ∀ᵐ a ∂ν, κ a ≪ η a) :
    ∫ x, f ((∂μ/∂ν) x * κ x Set.univ).toReal ∂ν
      ≤ ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η) := by
  rw [Measure.integral_compProd h_int]
  refine integral_mono_ae ?_ ?_ ?_
  · sorry
  · rw [integrable_f_rnDeriv_compProd_iff hf hf_cvx] at h_int
    rw [integrable_congr (integral_f_compProd_congr _ _ _ _)]
    exact h_int.2
  · exact f_rnDeriv_ae_le_integral μ ν κ η hf_cvx hf_cont h_int hκη

lemma integral_f_rnDeriv_le_integral_add [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (h_int_int : Integrable (fun a ↦ ∫ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b).toReal ∂η a) ν)
    (h_int_meas : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (hκη : ∀ᵐ a ∂ν, κ a ≪ η a) (h_deriv : derivAtTop f ≠ ⊤) :
    ∫ x, f ((∂μ/∂ν) x).toReal ∂ν
      ≤ ∫ x, f ((∂μ/∂ν) x * kernel.withDensity η (kernel.rnDeriv κ η) x Set.univ).toReal ∂ν
      + (derivAtTop f).toReal
        * ∫ a, ((∂μ/∂ν) a).toReal * (kernel.singularPart κ η a Set.univ).toReal ∂ν := by
  let κ' := kernel.withDensity η (kernel.rnDeriv κ η)
  have h : ∀ a, f ((∂μ/∂ν) a).toReal
      ≤ f ((∂μ/∂ν) a * κ' a Set.univ).toReal
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal
          * (kernel.singularPart κ η a Set.univ).toReal := by
    intro a
    simp only [ENNReal.toReal_mul]
    calc f ((∂μ/∂ν) a).toReal
      ≤ f (((∂μ/∂ν) a).toReal * (κ' a Set.univ).toReal)
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal
          * (1 - (κ' a Set.univ).toReal) :=
        le_add_derivAtTop' hf_cvx h_deriv ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    _ = f (((∂μ/∂ν) a).toReal * (κ' a Set.univ).toReal)
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal
          * (kernel.singularPart κ η a Set.univ).toReal := by
        congr
        norm_cast
        unfold_let κ'
        rw [sub_eq_iff_eq_add]
        rw [← ENNReal.one_toReal, ← measure_univ (μ := κ a)]
        conv_lhs => rw [← kernel.rnDeriv_add_singularPart κ η, add_comm]
        simp only [kernel.coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure, OuterMeasure.coe_add]
        rw [ENNReal.toReal_add]
        · exact measure_ne_top _ _
        · exact measure_ne_top _ _
  refine (integral_mono ?_ ?_ h).trans_eq ?_
  · sorry
  · sorry
  rw [integral_add]
  rotate_left
  · sorry
  · sorry
  unfold_let κ'
  simp_rw [mul_assoc]
  rw [integral_mul_left]

lemma le_fDiv_compProd [MeasurableSpace.CountablyGenerated β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (h_int_meas : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  by_cases h_top : fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) = ⊤
  · simp [h_top]
  rw [← ne_eq, fDiv_compProd_ne_top_iff hf hf_cvx] at h_top
  obtain ⟨h1, h2, h3⟩ := h_top
  let κ' := kernel.withDensity η (kernel.rnDeriv κ η)
  by_cases h_deriv : derivAtTop f = ⊤
  · sorry
  rw [fDiv_of_ne_top]
  swap; sorry
  calc ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * Measure.singularPart μ ν Set.univ
  _ ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := sorry

end ProbabilityTheory

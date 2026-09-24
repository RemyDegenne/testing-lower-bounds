/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Probability.Kernel.Integral
public import TestingLowerBounds.FDiv.CompProd
public import TestingLowerBounds.FDiv.Measurable
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import TestingLowerBounds.FDiv.DPIJensen

/-!

# Conditional f-divergence

## Main definitions

* `condFDiv f κ η μ`: the conditional f-divergence `∫⁻ x, fDiv f (κ x) (η x) ∂μ` between the
  kernels `κ` and `η` with respect to the measure `μ`.

## Main statements

* `condFDiv_ne_top_iff`, `condFDiv_eq_top_iff`: finiteness of the conditional f-divergence.
* `fDiv_compProd_right`: `fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = condFDiv f κ η μ`.
* `fDiv_comp_left_le`: `fDiv f (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condFDiv f κ η μ`.
* `condFDiv_measure_compProd`: the conditional f-divergence with respect to a
  composition-product `μ ⊗ₘ ξ` is an iterated conditional f-divergence.

-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : DivFunction}

section Conditional

/-- Conditional f-divergence. -/
noncomputable
def condFDiv (f : DivFunction) (κ η : Kernel α β) (μ : Measure α) : ℝ≥0∞ :=
  ∫⁻ x, fDiv f (κ x) (η x) ∂μ

/-- Equivalence between two possible versions of the first condition for the finiteness of the
conditional f divergence, the second version is the preferred one. -/
lemma fDiv_ae_ne_top_iff [IsFiniteKernel κ] [IsFiniteKernel η] :
    (∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ∞)
    ↔ (∀ᵐ a ∂μ, ∫⁻ x, f ((∂κ a/∂η a) x) ∂η a ≠ ∞) ∧ (f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  simp_rw [fDiv_ne_top_iff, eventually_and, eventually_all]

section CondFDivEq

variable [CountableOrCountablyGenerated α β]

/-- Equivalence between two possible versions of the second condition for the finiteness of the
conditional f divergence, the second version is the preferred one. -/
lemma lintegral_fDiv_ne_top_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫⁻ x, fDiv f (κ x) (η x) ∂μ ≠ ∞ ↔ ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂η a ∂μ ≠ ∞ := by
  by_cases h_top : f.derivAtTop = ∞
  · rw [lintegral_congr_ae]
    filter_upwards [h_ac h_top] with a ha
    rw [fDiv_of_absolutelyContinuous ha]
  · simp_rw [fDiv]
    rw [lintegral_add_right]
    swap
    · simp_rw [← Kernel.singularPart_eq_singularPart_measure]
      exact (Kernel.measurable_coe _ .univ).const_mul _
    simp only [ne_eq, ENNReal.add_eq_top, not_or, and_iff_left_iff_imp]
    intro _
    rw [lintegral_const_mul]
    swap
    · simp_rw [← Kernel.singularPart_eq_singularPart_measure]
      exact Kernel.measurable_coe _ .univ
    refine ENNReal.mul_ne_top h_top ?_
    rw [lintegral_singularPart _ _ _ .univ]
    simp

@[simp]
lemma condFDiv_of_not_ae_finite [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : ¬ ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ∞) :
    condFDiv f κ η μ = ∞ := by
  rw [condFDiv]
  by_contra h_not
  exact h <| (ae_lt_top (measurable_fDiv κ η) h_not).mono fun _ ha ↦ ha.ne

@[simp]
lemma condFDiv_of_not_ae_ac [IsFiniteKernel κ] [IsFiniteKernel η] (h_top : f.derivAtTop = ∞)
    (h : ¬ ∀ᵐ a ∂μ, κ a ≪ η a) :
    condFDiv f κ η μ = ∞ := by
  apply condFDiv_of_not_ae_finite
  rw [fDiv_ae_ne_top_iff]
  tauto

@[simp]
lemma condFDiv_of_lintegral_eq_top [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hf : ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂η a ∂μ = ∞) :
    condFDiv f κ η μ = ∞ := by
  by_cases h_top : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ∞
  swap; · exact condFDiv_of_not_ae_finite h_top
  by_contra h_ne
  exact (lintegral_fDiv_ne_top_iff (fDiv_ae_ne_top_iff.mp h_top).2).mp h_ne hf

lemma condFDiv_ne_top_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDiv f κ η μ ≠ ∞ ↔
      ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂(η a) ∂μ ≠ ∞
        ∧ (f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  refine ⟨fun h ↦ ⟨fun h_eq ↦ h (condFDiv_of_lintegral_eq_top h_eq), fun h_eq_top ↦ ?_⟩,
    fun ⟨h1, h2⟩ ↦ (lintegral_fDiv_ne_top_iff h2).mpr h1⟩
  by_contra h_not
  exact h <| condFDiv_of_not_ae_ac h_eq_top h_not

lemma condFDiv_eq_top_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDiv f κ η μ = ∞ ↔
      ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂(η a) ∂μ = ∞
        ∨ (f.derivAtTop = ∞ ∧ ¬ ∀ᵐ a ∂μ, κ a ≪ η a) := by
  have h := condFDiv_ne_top_iff (κ := κ) (η := η) (μ := μ) (f := f)
  tauto

lemma toReal_condFDiv_eq_integral [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : condFDiv f κ η μ ≠ ∞) :
    (condFDiv f κ η μ).toReal = ∫ x, (fDiv f (κ x) (η x)).toReal ∂μ := by
  rw [condFDiv, integral_toReal (measurable_fDiv _ _).aemeasurable]
  exact ae_lt_top (measurable_fDiv _ _) h

lemma condFDiv_eq_add [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDiv f κ η μ = ∫⁻ a, ∫⁻ y, f ((∂κ a/∂η a) y) ∂η a ∂μ
      + f.derivAtTop * ∫⁻ a, (κ a).singularPart (η a) .univ ∂μ := by
  simp_rw [condFDiv, fDiv]
  rw [lintegral_add_right]
  swap; · exact ((Measure.measurable_coe .univ).comp (κ.measurable_singularPart η)).const_mul _
  rw [lintegral_const_mul]
  exact (Measure.measurable_coe .univ).comp (κ.measurable_singularPart η)

lemma condFDiv_of_ae_ac [IsFiniteKernel κ] [IsFiniteKernel η] (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a) :
    condFDiv f κ η μ = ∫⁻ a, ∫⁻ y, f ((∂κ a/∂η a) y) ∂η a ∂μ := by
  rw [condFDiv_eq_add]
  suffices ∫⁻ a, ((κ a).singularPart (η a)) univ ∂μ = 0 by simp [this]
  rw [lintegral_eq_zero_iff]
  swap; · exact (Measure.measurable_coe .univ).comp (κ.measurable_singularPart η)
  filter_upwards [h_ac] with x hx
  simp only [Pi.zero_apply, Measure.measure_univ_eq_zero]
  exact Measure.singularPart_eq_zero_of_ac hx

end CondFDivEq

@[simp]
lemma condFDiv_self (κ : Kernel α β) (μ : Measure α) [IsFiniteKernel κ] :
    condFDiv f κ κ μ = 0 := by
  simp [condFDiv, fDiv_self]

@[simp]
lemma condFDiv_zero_left :
    condFDiv f 0 η μ = f 0 * ∫⁻ a, ((η a) .univ) ∂μ := by
  rw [condFDiv]
  simp only [zero_apply, fDiv_zero_measure_left]
  rw [lintegral_const_mul]
  exact Kernel.measurable_coe _ .univ

@[simp]
lemma condFDiv_zero_measure : condFDiv f κ η 0 = 0 := by simp [condFDiv]

@[simp]
lemma condFDiv_of_isEmpty_left [IsEmpty α] : condFDiv f κ η μ = 0 := by
  simp [condFDiv]

@[simp]
lemma condFDiv_of_isEmpty_right [IsEmpty β] [IsFiniteKernel κ] :
    condFDiv f κ η μ = 0 := by
  suffices κ = η from by exact this ▸ condFDiv_self κ _
  ext x s _
  simp [s.eq_empty_of_isEmpty]

@[simp]
lemma condFDiv_const {ξ : Measure β} :
    condFDiv f (Kernel.const β μ) (Kernel.const β ν) ξ = (fDiv f μ ν) * ξ .univ := by
  simp [condFDiv]

section CompProd

variable [CountableOrCountablyGenerated α β]

/-- For f-divergences, the divergence between two composition-products with same first measure is
equal to the conditional divergence. -/
theorem fDiv_compProd_right (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = condFDiv f κ η μ := by
  rw [fDiv, condFDiv_eq_add, Measure.lintegral_compProd measurable_divFunction_rnDeriv,
    lintegral_singularPart _ _ _ .univ, univ_prod_univ]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [Kernel.rnDeriv_measure_compProd_right' μ κ η] with a ha
  refine lintegral_congr_ae ?_
  filter_upwards [ha] with b hb
  rw [hb]

lemma condFDiv_ne_top_iff_fDiv_compProd_ne_top [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDiv f κ η μ ≠ ∞ ↔ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞ := by
  rw [fDiv_compProd_right]

lemma fDiv_comp_left_le (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condFDiv f κ η μ := by
  calc fDiv f (κ ∘ₘ μ) (η ∘ₘ μ)
    ≤ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) := fDiv_comp_le_compProd'' μ μ κ η
  _ = condFDiv f κ η μ := fDiv_compProd_right μ κ η

end CompProd

section CompProdMeasure

variable {γ : Type*} {mγ : MeasurableSpace γ}

/-- The conditional f-divergence with respect to a composition-product `μ ⊗ₘ ξ` is an iterated
conditional f-divergence. -/
lemma condFDiv_measure_compProd [CountableOrCountablyGenerated (α × β) γ] [SFinite μ]
    {ξ : Kernel α β} [IsSFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDiv f κ η (μ ⊗ₘ ξ) = ∫⁻ x, condFDiv f (κ.sectR x) (η.sectR x) (ξ x) ∂μ := by
  rw [condFDiv, Measure.lintegral_compProd (measurable_fDiv _ _)]
  rfl

end CompProdMeasure

end Conditional

section OfReal

/-! ### Conditional f-divergences for a `DivFunction` given by `DivFunction.ofReal` -/

variable {μ : Measure α} {κ η : Kernel α β}

lemma integrable_fDiv_ofReal_iff_of_ne_top [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    {f : ℝ → ℝ} {hf : ConvexOn ℝ (Set.Ioi 0) f} {hf_one : f 1 = 0}
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Set.Ioi 0) 0)
    (h_int : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (h_ne : (DivFunction.ofReal f hf hf_one).derivAtTop ≠ ∞) :
    Integrable (fun a ↦ (fDiv (.ofReal f hf hf_one) (κ a) (η a)).toReal) μ
      ↔ Integrable (fun a ↦ ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a)) μ := by
  have h : ∀ᵐ a ∂μ, (fDiv (.ofReal f hf hf_one) (κ a) (η a)).toReal
      = ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a)
        + (DivFunction.ofReal f hf hf_one).derivAtTop.toReal
          * ((κ a).singularPart (η a) .univ).toReal := by
    filter_upwards [h_int] with a h_int
    exact toReal_fDiv_ofReal_eq_integral_add hf_nonneg h_cont h_int h_ne
  rw [integrable_congr h, integrable_add_iff_integrable_left']
  refine Integrable.const_mul ?_ _
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · simp_rw [← Kernel.singularPart_eq_singularPart_measure]
    exact (Kernel.measurable_coe _ .univ).aemeasurable
  · rw [lintegral_singularPart _ _ _ .univ]
    simp

lemma integrable_fDiv_ofReal_iff_of_ac [IsFiniteKernel κ]
    {f : ℝ → ℝ} {hf : ConvexOn ℝ (Set.Ioi 0) f} {hf_one : f 1 = 0}
    (hf_nonneg : ∀ x, 0 ≤ x → 0 ≤ f x) (h_cont : ContinuousWithinAt f (Set.Ioi 0) 0)
    (h_int : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (hμη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun a ↦ (fDiv (.ofReal f hf hf_one) (κ a) (η a)).toReal) μ
      ↔ Integrable (fun a ↦ ∫ x, f ((∂κ a/∂η a) x).toReal ∂(η a)) μ := by
  refine integrable_congr ?_
  filter_upwards [h_int, hμη] with a h_int hμη
  exact toReal_fDiv_ofReal_eq_integral_add_of_ac hf_nonneg h_cont h_int hμη

end OfReal

end ProbabilityTheory

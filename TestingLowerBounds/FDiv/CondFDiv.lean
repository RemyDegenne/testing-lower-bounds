/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.FDiv.CompProd
import TestingLowerBounds.ForMathlib.Integrable_of_empty
import Mathlib.MeasureTheory.Order.Group.Lattice
/-!

# Conditional f-divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open Real MeasureTheory Filter MeasurableSpace Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : ℝ → ℝ}

section Conditional

-- TODO: explain that we should not use these hypotheses in lemmas, but equivalent ones.
open Classical in
/-- Conditional f-divergence. -/
noncomputable
def condFDiv (f : ℝ → ℝ) (κ η : Kernel α β) (μ : Measure α) : EReal :=
  if (∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    ∧ (Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ)
  then ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal)
  else ⊤

section CondFDivEq

@[simp]
lemma condFDiv_of_not_ae_finite (h : ¬ ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤) :
    condFDiv f κ η μ = ⊤ := if_neg (not_and_of_not_left _ h)

@[simp]
lemma condFDiv_of_not_ae_integrable [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : ¬ ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a)) :
    condFDiv f κ η μ = ⊤ := by
  apply condFDiv_of_not_ae_finite
  rw [fDiv_ae_ne_top_iff]
  tauto

@[simp]
lemma condFDiv_of_not_ae_ac [IsFiniteKernel κ] [IsFiniteKernel η] (h_top : derivAtTop f = ⊤)
    (h : ¬ ∀ᵐ a ∂μ, κ a ≪ η a) :
    condFDiv f κ η μ = ⊤ := by
  apply condFDiv_of_not_ae_finite
  rw [fDiv_ae_ne_top_iff]
  tauto

@[simp]
lemma condFDiv_of_not_integrable
    (hf : ¬ Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) :
    condFDiv f κ η μ = ⊤ := if_neg (not_and_of_not_right _ hf)

@[simp]
lemma condFDiv_of_not_integrable' [CountableOrCountablyGenerated α β] [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h_cvx : ConvexOn ℝ (Ici 0) f)
    (hf : ¬ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ) :
    condFDiv f κ η μ = ⊤ := by
  by_cases h_top : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤
  swap; exact condFDiv_of_not_ae_finite h_top
  apply condFDiv_of_not_integrable
  rwa [integrable_fDiv_iff h_cvx (fDiv_ae_ne_top_iff.mp h_top).1 (fDiv_ae_ne_top_iff.mp h_top).2]

/- Use condFDiv_eq instead: its assumptions are in normal form. -/
lemma condFDiv_eq' (hf_ae : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    (hf : Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) :
    condFDiv f κ η μ = ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal) :=
  if_pos ⟨hf_ae, hf⟩

variable [CountableOrCountablyGenerated α β]

lemma condFDiv_ne_top_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_cvx : ConvexOn ℝ (Ici 0) f) :
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
      rwa [integrable_fDiv_iff h_cvx (fDiv_ae_ne_top_iff.mp h'.1).1 (fDiv_ae_ne_top_iff.mp h'.1).2]
        at h_int
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
    rw [integrable_fDiv_iff h_cvx hf_int h_contra] at h
    exact h h_int

lemma condFDiv_eq_top_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_cvx : ConvexOn ℝ (Ici 0) f) :
    condFDiv f κ η μ = ⊤ ↔
      ¬ (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
        ∨ ¬ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂(η a)) μ
        ∨ (derivAtTop f = ⊤ ∧ ¬ ∀ᵐ a ∂μ, κ a ≪ η a) := by
  have h := condFDiv_ne_top_iff (κ := κ) (η := η) (μ := μ) (f := f) h_cvx
  tauto

lemma condFDiv_eq [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_ae : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (hf : Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ)
    (h_deriv : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    condFDiv f κ η μ = ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal) :=
  condFDiv_eq' (fDiv_ae_ne_top_iff.mpr ⟨hf_ae, h_deriv⟩)
    ((integrable_fDiv_iff h_cvx hf_ae h_deriv).mpr hf)

lemma condFDiv_ne_top_iff' [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_cvx : ConvexOn ℝ (Ici 0) f) :
    condFDiv f κ η μ ≠ ⊤
      ↔ condFDiv f κ η μ = ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal) := by
  constructor
  · rw [condFDiv_ne_top_iff h_cvx]
    exact fun ⟨h1, h2, h3⟩ => condFDiv_eq h_cvx h1 h2 h3
  · simp_all only [ne_eq, EReal.coe_ne_top, not_false_eq_true, implies_true]

lemma condFDiv_eq_add [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_ae : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (hf : Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ)
    (h_deriv : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    condFDiv f κ η μ = (μ[fun a ↦ ∫ y, f ((∂κ a/∂η a) y).toReal ∂η a] : ℝ)
      + (derivAtTop f).toReal * (μ[fun a ↦ ((κ a).singularPart (η a) Set.univ).toReal] : ℝ) := by
  rw [condFDiv_eq h_cvx hf_ae hf h_deriv]
  have : (fun x ↦ (fDiv f (κ x) (η x)).toReal)
      =ᵐ[μ] fun x ↦ ∫ y, f ((∂(κ x)/∂(η x)) y).toReal ∂(η x)
        + (derivAtTop f * (κ x).singularPart (η x) Set.univ).toReal := by
    have h_deriv' : ∀ᵐ a ∂μ, derivAtTop f = ⊤ → κ a ≪ η a := by
      simpa only [eventually_all] using h_deriv
    filter_upwards [hf_ae, h_deriv'] with x hx hx_deriv
    exact toReal_fDiv_of_integrable h_cvx hx hx_deriv
  rw [integral_congr_ae this, integral_add]
  rotate_left
  · exact hf
  · simp_rw [EReal.toReal_mul]
    convert (integrable_singularPart (κ := κ) (η := η) (μ := μ)).const_mul (derivAtTop f).toReal
    rw [← EReal.coe_ennreal_toReal, EReal.toReal_coe]
    exact measure_ne_top _ _
  simp only [EReal.coe_add, EReal.toReal_mul]
  rw [integral_mul_left]
  simp only [_root_.EReal.toReal_coe_ennreal, EReal.coe_mul]

lemma condFDiv_of_derivAtTop_eq_top [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_ae : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (hf : Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ)
    (h_top : derivAtTop f = ⊤) (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a) :
    condFDiv f κ η μ = (μ[fun a ↦ ∫ y, f ((∂κ a/∂η a) y).toReal ∂η a] : ℝ) := by
  rw [condFDiv_eq_add h_cvx hf_ae hf]
  · simp [h_top]
  · exact fun _ ↦ h_ac

end CondFDivEq

@[simp]
lemma condFDiv_self (κ : Kernel α β) (μ : Measure α) (hf_one : f 1 = 0) [IsFiniteKernel κ] :
    condFDiv f κ κ μ = 0 := by
  simp only [fDiv_self hf_one, ne_eq, EReal.zero_ne_top, not_false_eq_true, eventually_true,
    EReal.toReal_zero, integrable_zero, condFDiv_eq', integral_zero, EReal.coe_zero]

@[simp]
lemma condFDiv_zero_left [IsFiniteMeasure μ] [IsFiniteKernel η] :
    condFDiv f 0 η μ = f 0 * ∫ a, ((η a) Set.univ).toReal ∂μ := by
  rw [condFDiv_eq' _ _] <;> simp_rw [Kernel.zero_apply, fDiv_zero_measure]
  · simp_rw [EReal.toReal_mul, EReal.toReal_coe, EReal.toReal_coe_ennreal]
    norm_cast
    exact integral_mul_left (f 0) _
  · filter_upwards with _
    simp only [ne_eq, EReal.mul_eq_top, EReal.coe_ne_bot, false_and, EReal.coe_neg',
      EReal.coe_ennreal_ne_bot, and_false, EReal.coe_ne_top, EReal.coe_ennreal_pos,
      Measure.measure_univ_pos, EReal.coe_pos, EReal.coe_ennreal_eq_top_iff, measure_ne_top,
      or_self, not_false_eq_true]
  · simp_rw [EReal.toReal_mul, EReal.toReal_coe, EReal.toReal_coe_ennreal]
    apply MeasureTheory.Integrable.const_mul
    exact Kernel.IsFiniteKernel.integrable μ η MeasurableSet.univ

lemma condFDiv_zero_left' [IsProbabilityMeasure μ] [IsMarkovKernel η] :
    condFDiv f 0 η μ = f 0 := by
  simp

--I also wanted to add something like condKL_zero_right, but it turns out it's not so
--straightforward to state and prove, and since we don't really need it for now I will leave it out.

@[simp]
lemma condFDiv_zero_measure : condFDiv f κ η 0 = 0 := by
  have hf_ae : ∀ᵐ a ∂(0 : Measure α), fDiv f (κ a) (η a) ≠ ⊤ := by
    simp only [ne_eq, ae_zero, eventually_bot]
  rw [condFDiv_eq' hf_ae integrable_zero_measure]
  simp only [integral_zero_measure, EReal.coe_zero]

@[simp]
lemma condFDiv_of_isEmpty_left [IsEmpty α] : condFDiv f κ η μ = 0 := by
  suffices μ = 0 from this ▸ condFDiv_zero_measure
  ext s
  exact Set.eq_empty_of_isEmpty s ▸ measure_empty

@[simp]
lemma condFDiv_of_isEmpty_right [IsEmpty β] [IsFiniteKernel κ] (hf_one : f 1 = 0) :
    condFDiv f κ η μ = 0 := by
  suffices κ = η from by exact this ▸ condFDiv_self κ _ hf_one
  ext x s _
  simp [Set.eq_empty_of_isEmpty s]

lemma condFDiv_ne_bot (κ η : Kernel α β) (μ : Measure α) : condFDiv f κ η μ ≠ ⊥ := by
  rw [condFDiv]
  split_ifs with h
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
  · norm_num

lemma condFDiv_nonneg [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (hf_one : f 1 = 0) : 0 ≤ condFDiv f κ η μ := by
  by_cases h_ae : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤
  swap; · rw[condFDiv_of_not_ae_finite h_ae]; exact le_top
  by_cases h_int : Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ
  swap; · rw[condFDiv_of_not_integrable h_int]; exact le_top
  rw [condFDiv_eq' h_ae h_int]
  simp only [EReal.coe_nonneg]
  apply integral_nonneg _
  intro x
  have h := fDiv_nonneg (μ := κ x) (ν := η x) hf_cvx hf_cont hf_one
  simp [EReal.toReal_nonneg, h]

lemma condFDiv_const' {ξ : Measure β} [IsFiniteMeasure ξ] (h_ne_bot : fDiv f μ ν ≠ ⊥) :
    condFDiv f (Kernel.const β μ) (Kernel.const β ν) ξ = (fDiv f μ ν) * ξ Set.univ := by
  by_cases hξ_zero : ξ = 0
  · simp only [hξ_zero, condFDiv_zero_measure, Measure.coe_zero,
      Pi.zero_apply, EReal.coe_ennreal_zero, mul_zero]
  by_cases h_zero : fDiv f μ ν = 0
  · simp only [h_zero, zero_mul]
    rw [condFDiv_eq'] <;>
      simp only [Kernel.const_apply, h_zero, EReal.toReal_zero, integral_zero, EReal.coe_zero,
        ne_eq, EReal.zero_ne_top, not_false_eq_true, eventually_true, integrable_zero]
  by_cases h_top : fDiv f μ ν = ⊤
  · rw [h_top, EReal.top_mul_of_pos _]
    · simp only [condFDiv_of_not_ae_finite, Kernel.const_apply, h_top, ne_eq, not_true_eq_false,
        eventually_false_iff_eq_bot, ae_eq_bot, hξ_zero, not_false_eq_true]
    · simp only [EReal.coe_ennreal_pos, Measure.measure_univ_pos, ne_eq, hξ_zero,
        not_false_eq_true]
  rw [condFDiv_eq' (by simp [h_top]) _]
  swap; simp [integrable_const_iff, lt_top_iff_ne_top]
  simp only [Kernel.const_apply, integral_const, smul_eq_mul, mul_comm, EReal.coe_mul]
  congr
  · exact EReal.coe_toReal h_top h_ne_bot
  · exact EReal.coe_ennreal_toReal (measure_ne_top _ _)

@[simp]
lemma condFDiv_const {ξ : Measure β} [IsFiniteMeasure ξ] [IsFiniteMeasure μ]
    (h_cvx : ConvexOn ℝ (Ici 0) f) :
    condFDiv f (Kernel.const β μ) (Kernel.const β ν) ξ = (fDiv f μ ν) * ξ Set.univ :=
  condFDiv_const' (fDiv_ne_bot h_cvx)

section CompProd

/-! We show that the integrability of the functions used in `fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η)`
and in `condFDiv f κ η μ` are equivalent. -/

variable [CountableOrCountablyGenerated α β]

lemma condFDiv_ne_top_iff_fDiv_compProd_ne_top [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Ici 0) f) :
    condFDiv f κ η μ ≠ ⊤ ↔ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ⊤ := by
  rw [condFDiv_ne_top_iff h_cvx, fDiv_compProd_right_ne_top_iff hf h_cvx]

lemma condFDiv_eq_top_iff_fDiv_compProd_eq_top [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] (hf : StronglyMeasurable f)
    (h_cvx : ConvexOn ℝ (Ici 0) f) :
    condFDiv f κ η μ = ⊤ ↔ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = ⊤ := by
  rw [← not_iff_not]
  exact condFDiv_ne_top_iff_fDiv_compProd_ne_top hf h_cvx

lemma fDiv_compProd_left (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η]
    (hf : StronglyMeasurable f) (h_cvx : ConvexOn ℝ (Ici 0) f) :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = condFDiv f κ η μ := by
  by_cases hf_top : condFDiv f κ η μ = ⊤
  · rwa [hf_top, ← condFDiv_eq_top_iff_fDiv_compProd_eq_top hf h_cvx]
  have hf_top' := hf_top
  rw [← ne_eq, condFDiv_ne_top_iff h_cvx] at hf_top'
  rcases hf_top' with ⟨h1, h2, h3⟩
  have h_int : Integrable (fun x ↦ f ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x).toReal) (μ ⊗ₘ η) := by
    rw [integrable_f_rnDeriv_compProd_right_iff hf h_cvx]
    exact ⟨h1, h2⟩
  rw [fDiv_of_integrable h_int, condFDiv_eq_add h_cvx h1 h2 h3, Measure.integral_compProd h_int,
    integral_congr_ae (integral_f_compProd_right_congr _ _ _)]
  by_cases h_deriv : derivAtTop f = ⊤
  · simp only [h_deriv, EReal.toReal_top, EReal.coe_zero, zero_mul]
    suffices (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) = 0 by
      simp [this]
    rw [Measure.singularPart_eq_zero, Kernel.Measure.absolutelyContinuous_compProd_right_iff]
    exact h3 h_deriv
  · congr 1
    rw [EReal.coe_toReal h_deriv h_cvx.derivAtTop_ne_bot, integral_singularPart _ _ _ MeasurableSet.univ,
      EReal.coe_ennreal_toReal, Set.univ_prod_univ]
    exact measure_ne_top _ _

variable {γ : Type*} [MeasurableSpace γ]

lemma condFDiv_snd'_toReal_eq_ae [CountableOrCountablyGenerated β γ] {ξ : Kernel α β}
    [IsFiniteKernel ξ] {κ η : Kernel (α × β) γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_cvx : ConvexOn ℝ (Ici 0) f)
    (h_ac : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, κ (a, b) ≪ η (a, b))
    (h_int : ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, Integrable (fun x ↦ f ((∂κ (a, b)/∂η (a, b)) x).toReal) (η (a, b)))
    (h_int2 : ∀ᵐ a ∂μ, Integrable
      (fun b ↦ ∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)) (ξ a)) :
    ∀ᵐ a ∂μ, (condFDiv f (Kernel.snd' κ a) (Kernel.snd' η a) (ξ a)).toReal =
      ∫ b, (fDiv f (κ (a, b)) (η (a, b))).toReal ∂ξ a := by
  simp_rw [← Kernel.snd'_apply] at h_int2 h_int h_ac ⊢
  rw [← eventually_all] at h_ac
  filter_upwards [h_ac, h_int, h_int2] with a ha_ac ha_int ha_int2
  rw [condFDiv_eq h_cvx ha_int ha_int2 ha_ac, EReal.toReal_coe]

lemma condFDiv_kernel_snd'_integrable_iff [CountableOrCountablyGenerated (α × β) γ]
    [IsFiniteMeasure μ] {ξ : Kernel α β}  [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ac : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, κ (a, b) ≪ η (a, b))
    (h_int : ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, Integrable (fun x ↦ f ((∂κ (a, b)/∂η (a, b)) x).toReal) (η (a, b)))
    (h_int2 : ∀ᵐ a ∂μ, Integrable (fun b ↦ ∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)) (ξ a))
    (hf_meas : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0) :
    Integrable (fun a ↦ (condFDiv f (Kernel.snd' κ a) (Kernel.snd' η a) (ξ a)).toReal) μ ↔
      Integrable (fun a ↦ ∫ b, |∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)| ∂ξ a) μ := by
  by_cases h_empty : Nonempty α
  swap; simp only [not_nonempty_iff.mp h_empty, Integrable.of_isEmpty]
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  have h_le : ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, |∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)|
        - (fDiv f (κ (a, b)) (η (a, b))).toReal ≤ |(derivAtTop f).toReal|
      ∧ (fDiv f (κ (a, b)) (η (a, b))).toReal - |∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)|
        ≤ |(derivAtTop f).toReal| := by
    filter_upwards [fDiv_toReal_eq_ae hf_cvx h_ac h_int] with a ha_ereal_add
    filter_upwards [ha_ereal_add] with b hb_ereal_add
    apply abs_sub_le_iff.mp
    calc
      _ = |(|∫ (x : γ), f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)|
          - |(fDiv f (κ (a, b)) (η (a, b))).toReal|)| := by
        rw [abs_eq_self.mpr <| EReal.toReal_nonneg (fDiv_nonneg hf_cvx hf_cont hf_one)]
      _ ≤ |∫ (x : γ), f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)
          - (fDiv f (κ (a, b)) (η (a, b))).toReal| := by
        exact abs_abs_sub_abs_le_abs_sub _ _
      _ = |(derivAtTop f).toReal| * ((κ (a, b)).singularPart (η (a, b)) Set.univ).toReal := by
        rw [hb_ereal_add, sub_add_cancel_left, abs_neg, abs_mul, ENNReal.abs_toReal]
      _ ≤ |(derivAtTop f).toReal| * ((κ (a, b)) Set.univ).toReal := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        gcongr
        · exact measure_ne_top (κ (a, b)) Set.univ
        · exact Measure.singularPart_le (κ (a, b)) (η (a, b)) Set.univ
      _ = _ := by rw [measure_univ, ENNReal.one_toReal, mul_one]
  have h_int2' : ∀ᵐ a ∂μ, Integrable (fun b ↦ (fDiv f (κ (a, b)) (η (a, b))).toReal) (ξ a) := by
    filter_upwards [eventually_all.mpr h_ac, h_int, h_int2] with a ha_ae ha_int ha_int2
    simp_rw [← Kernel.snd'_apply] at ha_int2 ha_int ha_ae ⊢
    exact (integrable_fDiv_iff hf_cvx ha_int ha_ae).mpr ha_int2
  rw [integrable_congr <| condFDiv_snd'_toReal_eq_ae hf_cvx h_ac h_int h_int2]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- using `h_le` we reduce the problem to the integrability of a sum of an integral and
    -- `f'(∞) * (ξ x) (univ)`
    apply Integrable.mono'
      (g := fun a ↦ ∫ b, ((fDiv f (κ (a, b)) (η (a, b))).toReal + |(derivAtTop f).toReal|) ∂ξ a)
    rotate_left
    · refine (StronglyMeasurable.integral_kernel_prod_right ?_).aestronglyMeasurable
      refine Measurable.abs ?_ |>.stronglyMeasurable
      exact measurable_integral_f_rnDeriv κ η hf_meas
    · filter_upwards [h_le, h_int2, h_int2'] with a ha_le ha_int2 ha_int2'
      rw [norm_eq_abs, abs_eq_self.mpr <| integral_nonneg <| fun _ ↦ abs_nonneg _]
      refine integral_mono_ae ha_int2.abs (integrable_add_const_iff.mpr ha_int2') ?_
      filter_upwards [ha_le] with a hb_le using by linarith
    apply Integrable.congr (f := fun a ↦ ∫ b, (fDiv f (κ (a, b)) (η (a, b))).toReal ∂ξ a
        + ((ξ a) Set.univ).toReal * |(derivAtTop f).toReal|)
    swap
    · filter_upwards [h_int2'] with a ha_int2'
      rw [integral_add ha_int2' (integrable_const _), integral_const, smul_eq_mul]
    -- we already know the integrability of the integral (hp `h`) and the other part is just a
    -- constant times a finite Kernel applied to a fixed set, so it's easy to show that
    -- it's integrable
    exact h.add (Integrable.Kernel _ MeasurableSet.univ |>.mul_const _)
  · -- using `h_le'` we reduce the problem to the integrability of a sum of an integral and
    -- `f'(∞) * (ξ x) (univ)`
    apply Integrable.mono' (g := fun a ↦ ∫ b,
      (|∫ (x : γ), f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)| + |(derivAtTop f).toReal|) ∂ξ a)
    rotate_left
    · refine (StronglyMeasurable.integral_kernel_prod_right ?_).aestronglyMeasurable
      exact (measurable_fDiv _ _ hf_meas).ereal_toReal.stronglyMeasurable
    · filter_upwards [h_le, h_int2, h_int2'] with a ha_le ha_int2 ha_int2'
      rw [norm_eq_abs, abs_eq_self.mpr <| integral_nonneg <| fun _ ↦ EReal.toReal_nonneg <|
        fDiv_nonneg hf_cvx hf_cont hf_one]
      refine integral_mono_ae ha_int2' (integrable_add_const_iff.mpr <| ha_int2.abs) ?_
      filter_upwards [ha_le] with a hb_le using by linarith
    apply Integrable.congr (f := fun a ↦ ∫ b, |∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)|
      ∂ξ a + ((ξ a) Set.univ).toReal * |(derivAtTop f).toReal|)
    swap
    · filter_upwards [h_int2] with a ha_int2
      rw [integral_add ha_int2.abs (integrable_const _), integral_const, smul_eq_mul]
    -- same as above
    exact h.add (Integrable.Kernel _ MeasurableSet.univ |>.mul_const _)

lemma condFDiv_kernel_fst'_integrable_iff [CountableOrCountablyGenerated (α × β) γ]
    {μ : Measure β} [IsFiniteMeasure μ] {ξ : Kernel β α} [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ac : derivAtTop f = ⊤ → ∀ᵐ b ∂μ, ∀ᵐ a ∂ξ b, κ (a, b) ≪ η (a, b))
    (h_int : ∀ᵐ b ∂μ, ∀ᵐ a ∂ξ b, Integrable (fun x ↦ f ((∂κ (a, b)/∂η (a, b)) x).toReal) (η (a, b)))
    (h_int2 : ∀ᵐ b ∂μ, Integrable (fun a ↦ ∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)) (ξ b))
    (hf_meas : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0) :
    Integrable (fun b ↦ (condFDiv f (Kernel.fst' κ b) (Kernel.fst' η b) (ξ b)).toReal) μ ↔
      Integrable (fun b ↦ ∫ a, |∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)| ∂ξ b) μ := by
  simp_rw [← Kernel.snd'_swapRight]
  exact condFDiv_kernel_snd'_integrable_iff h_ac h_int h_int2 hf_meas hf_cvx hf_cont hf_one

lemma condFDiv_compProd_meas_eq_top [CountableOrCountablyGenerated (α × β) γ] [IsFiniteMeasure μ]
    {ξ : Kernel α β} [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf_meas : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0) :
    condFDiv f κ η (μ ⊗ₘ ξ) = ⊤
      ↔ ¬ (∀ᵐ a ∂μ, condFDiv f (Kernel.snd' κ a) (Kernel.snd' η a) (ξ a) ≠ ⊤) ∨
        ¬ Integrable (fun x ↦ (condFDiv f (Kernel.snd' κ x) (Kernel.snd' η x) (ξ x)).toReal) μ := by
  by_cases h_empty : Nonempty α
  swap; simp only [isEmpty_prod, not_nonempty_iff.mp h_empty, true_or, condFDiv_of_isEmpty_left,
    EReal.zero_ne_top, IsEmpty.forall_iff, eventually_of_forall, not_true_eq_false,
    Integrable.of_isEmpty, or_self]
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  rw [condFDiv_eq_top_iff hf_cvx]
  constructor
  · by_cases h_ac : derivAtTop f = ⊤ → ∀ᵐ x ∂(μ ⊗ₘ ξ), κ x ≪ η x
    swap
    · rw [Measure.ae_compProd_iff (Kernel.measurableSet_absolutelyContinuous _ _)] at h_ac
      simp_rw [condFDiv_ne_top_iff hf_cvx, Kernel.snd'_apply, eventually_and, not_and_or,
        eventually_all]
      intro; left; right; right
      exact h_ac
    have h_ac' := h_ac
    rw [Measure.ae_compProd_iff (Kernel.measurableSet_absolutelyContinuous _ _)] at h_ac
    by_cases h_int : ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a,
      Integrable (fun y ↦ f ((∂κ (a, b)/∂η (a, b)) y).toReal) (η (a, b))
    swap; · simp only [not_eventually, ne_eq, condFDiv_ne_top_iff hf_cvx, Kernel.snd'_apply,
        eventually_and, h_int, eventually_all, false_and, not_false_eq_true, true_or, implies_true]
    have h_int' := h_int
    rw [← Measure.ae_compProd_iff (measurableSet_integrable_f_rnDeriv κ η hf_meas)] at h_int'
    rw [← _root_.not_imp]
    simp_all only [forall_true_left, not_true_eq_false, implies_true, or_false, false_or, ne_eq,
      not_eventually, not_not]
    rw [Measure.integrable_compProd_iff
      (measurable_integral_f_rnDeriv κ η hf_meas).aestronglyMeasurable]
    push_neg
    intro h
    by_cases h_int2 :
      ∀ᵐ a ∂μ, Integrable (fun b ↦ ∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)) (ξ a)
    · simp_all only [forall_true_left, norm_eq_abs]
      right
      exact (condFDiv_kernel_snd'_integrable_iff
        h_ac h_int h_int2 hf_meas hf_cvx hf_cont hf_one).mp.mt h
    · left
      contrapose! h_int2
      simp_rw [not_frequently, condFDiv_ne_top_iff hf_cvx] at h_int2
      filter_upwards [h_int2] with a ha_int2
      simp_rw [← Kernel.snd'_apply, ha_int2.2.1]
  · intro h
    contrapose! h
    rcases h with ⟨h_int1, ⟨h_int2, h_ac⟩⟩
    rw [Measure.ae_compProd_iff (measurableSet_integrable_f_rnDeriv κ η hf_meas)] at h_int1
    rw [Measure.ae_compProd_iff (Kernel.measurableSet_absolutelyContinuous _ _)] at h_ac
    rw [Measure.integrable_compProd_iff h_int2.aestronglyMeasurable] at h_int2
    simp_all only [implies_true, forall_true_left, norm_eq_abs]
    refine ⟨?_, condFDiv_kernel_snd'_integrable_iff h_ac h_int1 h_int2.1 hf_meas hf_cvx hf_cont
      hf_one |>.mpr h_int2.2⟩
    filter_upwards [eventually_all.mpr h_ac, h_int1, h_int2.1] with a ha_ae ha_int ha_int2
    apply (condFDiv_ne_top_iff hf_cvx).mpr
    exact ⟨ha_int, ⟨ha_int2, ha_ae⟩⟩

-- -- TODO: find a better name
lemma condFDiv_compProd_meas [CountableOrCountablyGenerated (α × β) γ] [IsFiniteMeasure μ]
    {ξ : Kernel α β} [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf_meas : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousOn f (Ici 0)) (hf_one : f 1 = 0)
    (h_top : condFDiv f κ η (μ ⊗ₘ ξ) ≠ ⊤) :
    condFDiv f κ η (μ ⊗ₘ ξ)
      = ∫ x, (condFDiv f (Kernel.snd' κ x) (Kernel.snd' η x) (ξ x)).toReal ∂μ := by
  by_cases h_empty : Nonempty α
  swap; simp only [isEmpty_prod, not_nonempty_iff.mp h_empty, true_or, condFDiv_of_isEmpty_left,
    integral_of_isEmpty, EReal.coe_zero]
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  have h := ((condFDiv_ne_top_iff hf_cvx).mp h_top)
  rw [(condFDiv_ne_top_iff' hf_cvx).mp h_top,
    Measure.integral_compProd <| (integrable_fDiv_iff hf_cvx h.1 h.2.2).mpr h.2.1]
  replace h_top := (condFDiv_compProd_meas_eq_top hf_meas hf_cvx hf_cont hf_one).mpr.mt h_top
  push_neg at h_top
  norm_cast
  apply integral_congr_ae
  filter_upwards [h_top.1] with a ha
  simp_rw [(condFDiv_ne_top_iff' hf_cvx).mp ha, EReal.toReal_coe, Kernel.snd'_apply]

end CompProd

end Conditional

lemma fDiv_comp_left_le [Nonempty α] [StandardBorelSpace α] [CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condFDiv f κ η μ := by
  calc fDiv f (κ ∘ₘ μ) (η ∘ₘ μ)
    ≤ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) := fDiv_comp_le_compProd μ μ κ η hf hf_cvx hf_cont
  _ = condFDiv f κ η μ := fDiv_compProd_left μ κ η hf hf_cvx

end ProbabilityTheory

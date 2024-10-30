/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Probability.Kernel.Integral
import TestingLowerBounds.FDiv.CompProd.CompProd
import TestingLowerBounds.FDiv.Measurable
import TestingLowerBounds.ForMathlib.CountableOrCountablyGenerated

/-!

# Conditional f-divergence

-/

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

section CondFDivEq

variable [CountableOrCountablyGenerated α β]

@[simp]
lemma condFDiv_of_not_ae_finite [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : ¬ ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤) :
    condFDiv f κ η μ = ∞ := by
  rw [condFDiv]
  by_contra h_not
  refine h ?_
  have h_meas : Measurable (fun x ↦ fDiv f (κ x) (η x)) := measurable_fDiv κ η
  filter_upwards [ae_lt_top h_meas h_not] with a ha
  exact ha.ne

@[simp]
lemma condFDiv_of_not_ae_integrable [IsFiniteKernel κ] [IsFiniteKernel η]
    (h : ¬ ∀ᵐ a ∂μ, ∫⁻ x, f ((∂κ a/∂η a) x) ∂(η a) ≠ ∞) :
    condFDiv f κ η μ = ∞ := by
  apply condFDiv_of_not_ae_finite
  rw [fDiv_ae_ne_top_iff]
  tauto

@[simp]
lemma condFDiv_of_not_ae_ac [IsFiniteKernel κ] [IsFiniteKernel η] (h_top : f.derivAtTop = ⊤)
    (h : ¬ ∀ᵐ a ∂μ, κ a ≪ η a) :
    condFDiv f κ η μ = ∞ := by
  apply condFDiv_of_not_ae_finite
  rw [fDiv_ae_ne_top_iff]
  tauto

-- @[simp]
-- lemma condFDiv_of_not_integrable
--     (hf : ¬ Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) :
--     condFDiv f κ η μ = ∞ := if_neg (not_and_of_not_right _ hf)

@[simp]
lemma condFDiv_of_not_integrable' [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hf : ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂η a ∂μ = ∞) :
    condFDiv f κ η μ = ∞ := by
  by_cases h_top : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ∞
  swap; · exact condFDiv_of_not_ae_finite h_top
  rwa [condFDiv, ← not_not (a := ∫⁻ x, fDiv f (κ x) (η x) ∂μ = ⊤), ← ne_eq, integrable_fDiv_iff,
    ne_eq, not_not]
  rw [fDiv_ae_ne_top_iff] at h_top
  exact h_top.2

-- /- Use condFDiv_eq instead: its assumptions are in normal form. -/
-- lemma condFDiv_eq' (hf_ae : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ∞)
--     (hf : Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ) :
--     condFDiv f κ η μ = ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal) :=
--   if_pos ⟨hf_ae, hf⟩

lemma condFDiv_ne_top_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDiv f κ η μ ≠ ∞ ↔
      ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂(η a) ∂μ ≠ ∞
        ∧ (f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  · exact fun h_eq ↦ h (condFDiv_of_not_integrable' h_eq)
  · intro h_eq_top
    by_contra h_not
    exact h <| condFDiv_of_not_ae_ac h_eq_top h_not
  · rw [condFDiv]
    rwa [integrable_fDiv_iff h2]

lemma condFDiv_eq_top_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDiv f κ η μ = ∞ ↔
      ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂(η a) ∂μ = ∞
        ∨ (f.derivAtTop = ∞ ∧ ¬ ∀ᵐ a ∂μ, κ a ≪ η a) := by
  have h := condFDiv_ne_top_iff (κ := κ) (η := η) (μ := μ) (f := f)
  tauto

-- lemma condFDiv_eq [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
--     --(hf_ae : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
--     (hf : ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂η a ∂μ ≠ ∞)
--     (h_deriv : f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) :
--     condFDiv f κ η μ = ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal) :=
--   condFDiv_eq' (fDiv_ae_ne_top_iff.mpr ⟨hf_ae, h_deriv⟩)
--     ((integrable_fDiv_iff h_cvx hf_ae h_deriv).mpr hf)

-- lemma condFDiv_ne_top_iff' [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
--     condFDiv f κ η μ ≠ ∞
--       ↔ condFDiv f κ η μ = ((μ[fun x ↦ (fDiv f (κ x) (η x)).toReal] : ℝ) : EReal) := by
--   constructor
--   · rw [condFDiv_ne_top_iff h_cvx]
--     exact fun ⟨h1, h2, h3⟩ => condFDiv_eq h_cvx h1 h2 h3
--   · simp_all only [ne_eq, EReal.coe_ne_top, not_false_eq_true, implies_true]

lemma condFDiv_eq_add [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condFDiv f κ η μ = ∫⁻ a, ∫⁻ y, f ((∂κ a/∂η a) y) ∂η a ∂μ
      + f.derivAtTop * ∫⁻ a, (κ a).singularPart (η a) .univ ∂μ := by
  simp_rw [condFDiv, fDiv]
  rw [lintegral_add_right]
  swap; · exact ((Measure.measurable_coe .univ).comp (κ.measurable_singularPart η)).const_mul _
  rw [lintegral_const_mul]
  exact (Measure.measurable_coe .univ).comp (κ.measurable_singularPart η)

lemma condFDiv_of_derivAtTop_eq_top [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a) :
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
lemma condFDiv_zero_left [IsFiniteMeasure μ] [IsFiniteKernel η] :
    condFDiv f 0 η μ = f 0 * ∫⁻ a, ((η a) .univ) ∂μ := by
  rw [condFDiv]
  simp only [Kernel.zero_apply, fDiv_zero_measure_left]
  rw [lintegral_const_mul]
  exact Kernel.measurable_coe _ .univ

lemma condFDiv_zero_left' [IsProbabilityMeasure μ] [IsMarkovKernel η] :
    condFDiv f 0 η μ = f 0 := by
  simp

--I also wanted to add something like condKL_zero_right, but it turns out it's not so
--straightforward to state and prove, and since we don't really need it for now I will leave it out.

@[simp]
lemma condFDiv_zero_measure : condFDiv f κ η 0 = 0 := by simp [condFDiv]

@[simp]
lemma condFDiv_of_isEmpty_left [IsEmpty α] : condFDiv f κ η μ = 0 := by
  suffices μ = 0 from this ▸ condFDiv_zero_measure
  ext s
  exact s.eq_empty_of_isEmpty ▸ measure_empty

@[simp]
lemma condFDiv_of_isEmpty_right [IsEmpty β] [IsFiniteKernel κ] :
    condFDiv f κ η μ = 0 := by
  suffices κ = η from by exact this ▸ condFDiv_self κ _
  ext x s _
  simp [s.eq_empty_of_isEmpty]

-- lemma condFDiv_ne_bot (κ η : Kernel α β) (μ : Measure α) : condFDiv f κ η μ ≠ ⊥ := by
--   rw [condFDiv]
--   split_ifs with h
--   · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
--   · norm_num

-- lemma condFDiv_nonneg [IsMarkovKernel κ] [IsMarkovKernel η] : 0 ≤ condFDiv f κ η μ := by
--   by_cases h_ae : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ∞
--   swap; · rw[condFDiv_of_not_ae_finite h_ae]; exact le_top
--   by_cases h_int : Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ
--   swap; · rw[condFDiv_of_not_integrable h_int]; exact le_top
--   rw [condFDiv_eq' h_ae h_int]
--   simp only [EReal.coe_nonneg]
--   apply integral_nonneg _
--   intro x
--   have h := fDiv_nonneg (μ := κ x) (ν := η x) hf_cvx hf_cont hf_one
--   simp [EReal.toReal_nonneg, h]

@[simp]
lemma condFDiv_const {ξ : Measure β} :
    condFDiv f (Kernel.const β μ) (Kernel.const β ν) ξ = (fDiv f μ ν) * ξ .univ := by
  simp [condFDiv]

section CompProd

/-! We show that the integrability of the functions used in `fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η)`
and in `condFDiv f κ η μ` are equivalent. -/

section

variable [CountableOrCountablyGenerated α β]

lemma condFDiv_ne_top_iff_fDiv_compProd_ne_top [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    condFDiv f κ η μ ≠ ∞ ↔ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞ := by
  rw [condFDiv_ne_top_iff, fDiv_compProd_right_ne_top_iff]

lemma condFDiv_eq_top_iff_fDiv_compProd_eq_top [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    condFDiv f κ η μ = ∞ ↔ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∞ := by
  rw [← not_iff_not]
  exact condFDiv_ne_top_iff_fDiv_compProd_ne_top

/-- For f-divergences, the divergence between two composition-products with same first measure is
equal to the conditional divergence. -/
theorem fDiv_compProd_left (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) = condFDiv f κ η μ := by
  by_cases hf_top : condFDiv f κ η μ = ∞
  · rwa [hf_top, ← condFDiv_eq_top_iff_fDiv_compProd_eq_top]
  rw [← ne_eq, condFDiv_ne_top_iff] at hf_top
  rcases hf_top with ⟨_, h2⟩
  rw [fDiv, condFDiv_eq_add, Measure.lintegral_compProd]
  swap; · exact measurable_divFunction_rnDeriv
  have : ∫⁻ a, ∫⁻ b, f ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b)) ∂η a ∂μ
      = ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂η a ∂μ := by
    have h_eq := Kernel.rnDeriv_measure_compProd_right' μ κ η
    refine lintegral_congr_ae ?_
    filter_upwards [h_eq] with x hx
    refine lintegral_congr_ae ?_
    filter_upwards [hx] with y hy
    rw [hy]
  rw [this]
  congr 1
  by_cases h_deriv : f.derivAtTop = ∞
  · rw [h_deriv]
    have h1 : (μ ⊗ₘ κ).singularPart (μ ⊗ₘ η) = 0 := by
      rw [Measure.singularPart_eq_zero, Measure.absolutelyContinuous_compProd_right_iff]
      exact h2 h_deriv
    have h2 : ∫⁻ a, ((κ a).singularPart (η a)) univ ∂μ = 0 := by
      rw [lintegral_eq_zero_iff]
      swap; · exact (Measure.measurable_coe .univ).comp (κ.measurable_singularPart η)
      filter_upwards [h2 h_deriv] with x hx
      simp only [Pi.zero_apply, Measure.measure_univ_eq_zero]
      exact Measure.singularPart_eq_zero_of_ac hx
    simp [h1, h2]
  · rw [lintegral_singularPart _ _ _ .univ, Set.univ_prod_univ]

end

end CompProd

lemma fDiv_comp_left_le [Nonempty α] [StandardBorelSpace α] [CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condFDiv f κ η μ := by
  calc fDiv f (κ ∘ₘ μ) (η ∘ₘ μ)
    ≤ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) := fDiv_comp_le_compProd μ μ κ η
  _ = condFDiv f κ η μ := fDiv_compProd_left μ κ η

end Conditional

end ProbabilityTheory

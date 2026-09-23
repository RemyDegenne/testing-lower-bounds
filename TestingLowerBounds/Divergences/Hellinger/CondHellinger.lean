/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.KullbackLeibler.CondKL
import TestingLowerBounds.Divergences.Hellinger.Hellinger

/-!
# Conditional Hellinger divergence

## Main definitions

* `condHellingerDiv a κ η μ`: the conditional Hellinger divergence of order `a` between the
  kernels `κ` and `η` with respect to `μ`, defined as the conditional f-divergence for the
  divergence function `hellingerDivFun a`.

## Main statements

* `hellingerDiv_compProd_left`: `hellingerDiv a (μ ⊗ₘ κ) (μ ⊗ₘ η) = condHellingerDiv a κ η μ`.
* `hellingerDiv_comp_left_le`: `hellingerDiv a (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condHellingerDiv a κ η μ`.
* `condHellingerDiv_one`: the conditional Hellinger divergence of order `1` is `condKL`.

-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}
  {a : ℝ}

lemma hellingerDiv_ae_ne_top_iff'' (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞)
      ↔ (∀ᵐ x ∂μ, ∫⁻ b, hellingerDivFun a ((∂κ x/∂η x) b) ∂(η x) ≠ ∞)
        ∧ (1 ≤ a → ∀ᵐ x ∂μ, (κ x) ≪ (η x)) := by
  simp_rw [hellingerDiv_ne_top_iff, eventually_and, eventually_all]

/-- Conditional Hellinger divergence of order `a`. -/
noncomputable def condHellingerDiv (a : ℝ) (κ η : Kernel α β) (μ : Measure α) : ℝ≥0∞ :=
  condFDiv (hellingerDivFun a) κ η μ

lemma hellingerDiv_compProd_left [CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [∀ x, NeZero (κ x)] [IsFiniteKernel η] :
    hellingerDiv a (μ ⊗ₘ κ) (μ ⊗ₘ η) = condHellingerDiv a κ η μ := by
  rw [hellingerDiv, condHellingerDiv, fDiv_compProd_left _ _ _]

lemma hellingerDiv_comp_left_le [Nonempty α] [StandardBorelSpace α]
    [CountableOrCountablyGenerated α β] (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    hellingerDiv a (κ ∘ₘ μ) (η ∘ₘ μ) ≤ condHellingerDiv a κ η μ :=
  fDiv_comp_left_le μ κ η

/-! The normal form of the finiteness conditions for the conditional Hellinger divergence, when
`μ`, `κ` and `η` are finite and `a ∈ (0, 1) ∪ (1, +∞)`, is given by `condHellingerDiv_ne_top_iff`:
`condHellingerDiv a κ η μ ≠ ∞` iff
* `∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x)` (`h_int`),
* `1 ≤ a → ∀ᵐ x ∂μ, (κ x) ≪ (η x)` (`h_ac`),
* `Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ` (`h_int'`).

Under these conditions, `toReal_condHellingerDiv_eq_integral'` gives the integral form
`(condHellingerDiv a κ η μ).toReal = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
  + ((μ ⊗ₘ η) univ).toReal + (1 - a)⁻¹ * a * ((μ ⊗ₘ κ) univ).toReal`.
-/
section CondHellingerEq

lemma condHellingerDiv_one [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv 1 κ η μ = condKL κ η μ := by
  rw [condHellingerDiv, hellingerDivFun_one, condKL_eq_condFDiv]

lemma condHellingerDiv_of_not_ae_finite [CountableOrCountablyGenerated α β]
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ae : ¬ ∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞) :
    condHellingerDiv a κ η μ = ∞ := by
  rw [condHellingerDiv]
  exact condFDiv_of_not_ae_finite h_ae

lemma hellingerDiv_ae_ne_top_iff [IsFiniteKernel κ] [IsFiniteKernel η]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1) :
    (∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞)
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
        ∧ (1 ≤ a → ∀ᵐ x ∂μ, κ x ≪ η x) := by
  rw [hellingerDiv_ae_ne_top_iff'']
  simp_rw [lintegral_hellingerDivFun_ne_top_iff ha_pos ha_ne]

lemma hellingerDiv_ae_ne_top_of_lt_one [IsFiniteKernel κ] [IsFiniteKernel η] (ha : a < 1) :
    ∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞ :=
  ae_of_all _ fun _ ↦ hellingerDiv_ne_top_of_lt_one ha _ _

lemma integrable_toReal_hellingerDiv_iff [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (ha_pos : 0 < a) (ha_ne : a ≠ 1) (h_ae : ∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞) :
    Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ
      ↔ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
  have h : (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal)
      =ᵐ[μ] fun x ↦ (a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x
        + ((η x) .univ).toReal + (1 - a)⁻¹ * a * ((κ x) .univ).toReal := by
    filter_upwards [h_ae] with x hx
    exact toReal_hellingerDiv_eq_integral_of_ne_top ha_pos ha_ne hx
  rw [integrable_congr h,
    integrable_add_iff_integrable_left' ((Integrable.Kernel _ .univ).const_mul _),
    integrable_add_iff_integrable_left' (Integrable.Kernel _ .univ),
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (inv_ne_zero (sub_ne_zero.mpr ha_ne)))]

lemma condHellingerDiv_ne_top_iff [CountableOrCountablyGenerated α β] [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] (ha_pos : 0 < a) (ha_ne : a ≠ 1) :
    condHellingerDiv a κ η μ ≠ ∞
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
        ∧ (1 ≤ a → ∀ᵐ x ∂μ, κ x ≪ η x)
        ∧ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
  have h_meas : Measurable fun x ↦ hellingerDiv a (κ x) (η x) := measurable_fDiv _ _
  have h_eq : condHellingerDiv a κ η μ = ∫⁻ x, hellingerDiv a (κ x) (η x) ∂μ := rfl
  rw [h_eq]
  constructor
  · intro h
    have h_ae : ∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞ :=
      (ae_lt_top h_meas h).mono fun x hx ↦ hx.ne
    obtain ⟨h_int, h_ac⟩ := (hellingerDiv_ae_ne_top_iff ha_pos ha_ne).mp h_ae
    exact ⟨h_int, h_ac, (integrable_toReal_hellingerDiv_iff ha_pos ha_ne h_ae).mp
      ((integrable_toReal_iff h_meas.aemeasurable h_ae).mpr h)⟩
  · rintro ⟨h_int, h_ac, h_int'⟩
    have h_ae := (hellingerDiv_ae_ne_top_iff ha_pos ha_ne).mpr ⟨h_int, h_ac⟩
    exact (integrable_toReal_iff h_meas.aemeasurable h_ae).mp
      ((integrable_toReal_hellingerDiv_iff ha_pos ha_ne h_ae).mpr h_int')

lemma condHellingerDiv_eq_top_iff [CountableOrCountablyGenerated α β] [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] (ha_pos : 0 < a) (ha_ne : a ≠ 1) :
    condHellingerDiv a κ η μ = ∞
      ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
        ∨ (1 ≤ a ∧ ¬ ∀ᵐ x ∂μ, κ x ≪ η x)
        ∨ ¬ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
  rw [← not_not (a := _ = ∞), ← ne_eq, condHellingerDiv_ne_top_iff ha_pos ha_ne]
  tauto

lemma condHellingerDiv_ne_top_iff_of_one_lt [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] (ha : 1 < a) :
    condHellingerDiv a κ η μ ≠ ∞
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
        ∧ (∀ᵐ x ∂μ, κ x ≪ η x)
        ∧ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
  rw [condHellingerDiv_ne_top_iff (zero_lt_one.trans ha) ha.ne', imp_iff_right ha.le]

lemma condHellingerDiv_eq_top_iff_of_one_lt [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] (ha : 1 < a) :
    condHellingerDiv a κ η μ = ∞
      ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x))
        ∨ ¬ (∀ᵐ x ∂μ, κ x ≪ η x)
        ∨ ¬ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
  rw [← not_not (a := _ = ∞), ← ne_eq, condHellingerDiv_ne_top_iff_of_one_lt ha]
  tauto

lemma condHellingerDiv_ne_top_iff_of_lt_one [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] (ha_pos : 0 < a) (ha_lt : a < 1) :
    condHellingerDiv a κ η μ ≠ ∞
      ↔ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
  rw [condHellingerDiv_ne_top_iff ha_pos ha_lt.ne]
  simp only [not_le.mpr ha_lt, false_imp_iff, true_and]
  exact and_iff_right (ae_of_all _ fun x ↦ integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha_lt)

lemma condHellingerDiv_eq_top_iff_of_lt_one [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] (ha_pos : 0 < a) (ha_lt : a < 1) :
    condHellingerDiv a κ η μ = ∞
      ↔ ¬ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
  rw [← not_not (a := _ = ∞), ← ne_eq, condHellingerDiv_ne_top_iff_of_lt_one ha_pos ha_lt]

lemma condHellingerDiv_of_not_ae_integrable [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] (ha_pos : 0 < a) (ha_ne : a ≠ 1)
    (h_int : ¬ ∀ᵐ x ∂μ, Integrable (fun b ↦ ((∂κ x/∂η x) b).toReal ^ a) (η x)) :
    condHellingerDiv a κ η μ = ∞ :=
  (condHellingerDiv_eq_top_iff ha_pos ha_ne).mpr (Or.inl h_int)

lemma condHellingerDiv_of_not_ae_ac_of_one_le [CountableOrCountablyGenerated α β]
    [IsFiniteKernel κ] [IsFiniteKernel η] (ha : 1 ≤ a) (h_ac : ¬ ∀ᵐ x ∂μ, κ x ≪ η x) :
    condHellingerDiv a κ η μ = ∞ := by
  apply condHellingerDiv_of_not_ae_finite
  rw [hellingerDiv_ae_ne_top_iff'']
  tauto

lemma condHellingerDiv_of_not_integrable [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] (ha_pos : 0 < a) (ha_ne : a ≠ 1)
    (h_int : ¬ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condHellingerDiv a κ η μ = ∞ :=
  (condHellingerDiv_eq_top_iff ha_pos ha_ne).mpr (Or.inr (Or.inr h_int))

lemma toReal_condHellingerDiv_eq_integral [CountableOrCountablyGenerated α β]
    [IsFiniteKernel κ] [IsFiniteKernel η] (h : condHellingerDiv a κ η μ ≠ ∞) :
    (condHellingerDiv a κ η μ).toReal = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ :=
  toReal_condFDiv_eq_integral h

/-- Integral form of the conditional Hellinger divergence, when it is finite. -/
lemma toReal_condHellingerDiv_eq_integral' [CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] (ha_pos : 0 < a) (ha_ne : a ≠ 1)
    (h : condHellingerDiv a κ η μ ≠ ∞) :
    (condHellingerDiv a κ η μ).toReal
      = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
        + ((μ ⊗ₘ η) .univ).toReal + (1 - a)⁻¹ * a * ((μ ⊗ₘ κ) .univ).toReal := by
  have h_meas : Measurable fun x ↦ hellingerDiv a (κ x) (η x) := measurable_fDiv _ _
  have h_ae : ∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ∞ :=
    (ae_lt_top h_meas h).mono fun x hx ↦ hx.ne
  obtain ⟨-, -, h_int'⟩ := (condHellingerDiv_ne_top_iff ha_pos ha_ne).mp h
  rw [toReal_condHellingerDiv_eq_integral h]
  calc ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ
  _ = ∫ x, (a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x
        + ((η x) .univ).toReal + (1 - a)⁻¹ * a * ((κ x) .univ).toReal ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [h_ae] with x hx
    exact toReal_hellingerDiv_eq_integral_of_ne_top ha_pos ha_ne hx
  _ = _ := by
    rw [integral_add, integral_add, integral_const_mul, integral_const_mul,
      Measure.compProd_univ_toReal, Measure.compProd_univ_toReal]
    · exact h_int'.const_mul _
    · exact Integrable.Kernel _ .univ
    · exact (h_int'.const_mul _).add (Integrable.Kernel _ .univ)
    · exact (Integrable.Kernel _ .univ).const_mul _

end CondHellingerEq

end ProbabilityTheory

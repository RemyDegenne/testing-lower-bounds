/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym

/-!

-/

@[expose] public section

open Real MeasureTheory Filter Set

open scoped ENNReal MeasureTheory

namespace MeasureTheory.Measure

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

lemma rnDeriv_eq_zero_ae_of_zero_measure (ν : Measure α) {s : Set α} (hs : MeasurableSet s)
    (hμ : μ s = 0) : ∀ᵐ x ∂ν, x ∈ s → (μ.rnDeriv ν) x = 0 := by
  rw [← setLIntegral_eq_zero_iff hs (μ.measurable_rnDeriv ν)]
  exact le_antisymm (hμ ▸ Measure.setLIntegral_rnDeriv_le s) zero_le

/-- Singular part set of μ with respect to ν. -/
def singularPartSet (μ ν : Measure α) := {x | ν.rnDeriv (μ + ν) x = 0}

lemma measurableSet_singularPartSet : MeasurableSet (singularPartSet μ ν) :=
  measurable_rnDeriv _ _ (measurableSet_singleton _)

lemma measure_singularPartSet (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ν (singularPartSet μ ν) = 0 := by
  let s := singularPartSet μ ν
  have hs : MeasurableSet s := measurableSet_singularPartSet
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  have h1 : ∫⁻ x in s, ν.rnDeriv (μ + ν) x ∂(μ + ν) = 0 := by
    calc ∫⁻ x in s, ν.rnDeriv (μ + ν) x ∂(μ + ν)
      = ∫⁻ _ in s, 0 ∂(μ + ν) := setLIntegral_congr_fun hs fun ⦃_⦄ ↦ id
    _ = 0 := lintegral_zero
  have h2 : ∫⁻ x in s, ν.rnDeriv (μ + ν) x ∂(μ + ν) = ν s :=
    Measure.setLIntegral_rnDeriv hν_ac _
  exact h2.symm.trans h1

lemma absolutelyContinuous_restrict_compl_singularPartSet
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.restrict (singularPartSet μ ν)ᶜ ≪ ν := by
  refine AbsolutelyContinuous.mk fun A hA hA0 ↦ ?_
  rw [restrict_apply hA]
  have h1 : ∫⁻ x in A, ν.rnDeriv (μ + ν) x ∂(μ + ν) = 0 := by
    rw [Measure.setLIntegral_rnDeriv (by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _)]
    exact hA0
  rw [lintegral_eq_zero_iff (ν.measurable_rnDeriv _)] at h1
  have h2 : (μ + ν) (A ∩ (singularPartSet μ ν)ᶜ) = 0 := by
    rw [inter_comm, ← restrict_apply' hA, ← compl_mem_ae_iff, compl_compl]
    filter_upwards [h1] with x hx
    simpa [singularPartSet] using hx
  rw [Measure.add_apply, add_eq_zero] at h2
  exact h2.1

lemma restrict_singularPartSet_eq_singularPart (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.restrict (singularPartSet μ ν) = μ.singularPart ν := by
  symm
  refine singularPart_eq_restrict ?_ (measure_singularPartSet μ ν)
  have h := singularPart_restrict μ ν (measurableSet_singularPartSet (μ := μ) (ν := ν)).compl
  rw [singularPart_eq_zero_of_ac (absolutelyContinuous_restrict_compl_singularPartSet μ ν)] at h
  rw [← restrict_apply_univ, ← h]
  simp

lemma restrict_compl_singularPartSet_eq_withDensity
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.restrict (singularPartSet μ ν)ᶜ = ν.withDensity (μ.rnDeriv ν) := by
  have h := congr_arg (fun m ↦ m.restrict (singularPartSet μ ν)ᶜ)
    (haveLebesgueDecomposition_add μ ν)
  rw [h, restrict_add, ← restrict_singularPartSet_eq_singularPart,
    restrict_restrict measurableSet_singularPartSet.compl, compl_inter_self, restrict_empty,
    zero_add]
  refine restrict_eq_self_of_ae_mem ?_
  exact compl_mem_ae_iff.2 (withDensity_absolutelyContinuous ν _ (measure_singularPartSet μ ν))

lemma measure_inter_compl_singularPartSet (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {t : Set α} (ht : MeasurableSet t) :
    μ (t ∩ (singularPartSet μ ν)ᶜ) = ∫⁻ x in t, μ.rnDeriv ν x ∂ν := by
  rw [← restrict_apply ht, restrict_compl_singularPartSet_eq_withDensity, withDensity_apply _ ht]

example [SigmaFinite μ] [SigmaFinite ν] :
    μ (singularPartSet μ ν) = μ.singularPart ν .univ := by
  rw [← restrict_singularPartSet_eq_singularPart]
  simp only [MeasurableSet.univ, restrict_apply, Set.univ_inter]

lemma rnDeriv_eq_zero_ae_of_singularPartSet (μ ν ξ : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ∀ᵐ x ∂ξ, x ∈ μ.singularPartSet ν → (ν.rnDeriv ξ) x = 0 :=
  ν.rnDeriv_eq_zero_ae_of_zero_measure ξ Measure.measurableSet_singularPartSet
    (μ.measure_singularPartSet ν)

lemma rnDeriv_toReal_pos [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∀ᵐ x ∂μ, 0 < (μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_pos hμν, hμν.ae_le (rnDeriv_ne_top μ ν)] with x h0 htop
  simp_all only [pos_iff_ne_zero, ne_eq, not_false_eq_true, ENNReal.toReal_pos]

lemma ae_integrable_mul_rnDeriv_of_ae_integrable {κ : α → Measure β} [SigmaFinite μ] [SigmaFinite ν]
    (g : α → β → ℝ) (h : ∀ᵐ a ∂μ, Integrable (fun x ↦ g a x) (κ a)) :
    ∀ᵐ a ∂ν, Integrable (fun x ↦ (μ.rnDeriv ν a).toReal * g a x) (κ a) := by
  apply μ.ae_rnDeriv_ne_zero_imp_of_ae (ν := ν) at h
  filter_upwards [h] with a ha
  by_cases h_zero : μ.rnDeriv ν a = 0
  · rw [h_zero]
    simp only [ENNReal.toReal_zero, zero_mul]
    exact integrable_zero _ _ _
  · apply Integrable.const_mul
    exact ha h_zero

lemma ae_integrable_of_ae_integrable_mul_rnDeriv {κ : α → Measure β} [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (g : α → β → ℝ)
    (h : ∀ᵐ a ∂ν, Integrable (fun x ↦ (μ.rnDeriv ν a).toReal * g a x) (κ a)) :
    ∀ᵐ a ∂μ, Integrable (g a) (κ a) := by
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_toReal_pos hμν] with a ha h_pos
  apply (integrable_const_mul_iff _ (g a)).mp ha
  exact isUnit_iff_ne_zero.mpr h_pos.ne'

end MeasureTheory.Measure

/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym

/-!

-/

open Real MeasureTheory Filter Set

open scoped ENNReal MeasureTheory

namespace MeasureTheory.Measure

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

lemma rnDeriv_eq_zero_ae_of_zero_measure (ν : Measure α) {s : Set α} (hs : MeasurableSet s)
    (hμ : μ s = 0) : ∀ᵐ x ∂ν, x ∈ s → (μ.rnDeriv ν) x = 0 := by
  rw [← setLIntegral_eq_zero_iff hs (μ.measurable_rnDeriv ν)]
  exact le_antisymm (hμ ▸ Measure.setLIntegral_rnDeriv_le s) zero_le

/--Singular part set of μ with respect to ν.-/
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

lemma measure_inter_compl_singularPartSet' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {t : Set α} (ht : MeasurableSet t) :
    μ (t ∩ (singularPartSet μ ν)ᶜ) = ∫⁻ x in t ∩ (singularPartSet μ ν)ᶜ, μ.rnDeriv ν x ∂ν := by
  let s := singularPartSet μ ν
  have hs : MeasurableSet s := measurableSet_singularPartSet
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  have : μ (t ∩ sᶜ) = ∫⁻ x in t ∩ sᶜ,
      ν.rnDeriv (μ + ν) x * (μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x) ∂(μ + ν) := by
    have : ∫⁻ x in t ∩ sᶜ,
          ν.rnDeriv (μ + ν) x * (μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x) ∂(μ + ν)
        = ∫⁻ x in t ∩ sᶜ, μ.rnDeriv (μ + ν) x ∂(μ + ν) := by
      refine setLIntegral_congr_fun (ht.inter hs.compl) ?_
      -- Not sure...
      sorry
      -- filter_upwards [ν.rnDeriv_lt_top (μ + ν)] with x hx_top hx
      -- rw [div_eq_mul_inv, mul_comm, mul_assoc, ENNReal.inv_mul_cancel, mul_one]
      -- · simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, s] at hx
      --   exact hx.2
      -- · exact hx_top.ne
    rw [this, Measure.setLIntegral_rnDeriv (rfl.absolutelyContinuous.add_right _)]
  rw [this, setLIntegral_rnDeriv_mul hν_ac _ (ht.inter hs.compl)]
  swap; · exact ((μ.measurable_rnDeriv _).div (ν.measurable_rnDeriv _)).aemeasurable
  refine setLIntegral_congr_fun (ht.inter hs.compl) ?_
  sorry
  -- filter_upwards [μ.rnDeriv_eq_div ν] with x hx
  -- exact hx ▸ fun _ ↦ rfl

lemma measure_inter_compl_singularPartSet (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {t : Set α} (ht : MeasurableSet t) :
    μ (t ∩ (singularPartSet μ ν)ᶜ) = ∫⁻ x in t, μ.rnDeriv ν x ∂ν := by
  rw [measure_inter_compl_singularPartSet' _ _ ht]
  symm
  calc ∫⁻ x in t, rnDeriv μ ν x ∂ν
    = ∫⁻ x in (singularPartSet μ ν) ∩ t, rnDeriv μ ν x ∂ν
      + ∫⁻ x in (singularPartSet μ ν)ᶜ ∩ t, rnDeriv μ ν x ∂ν := by
        rw [← restrict_restrict measurableSet_singularPartSet,
          ← restrict_restrict measurableSet_singularPartSet.compl,
          lintegral_add_compl _ measurableSet_singularPartSet]
  _ = ∫⁻ x in t ∩ (singularPartSet μ ν)ᶜ, rnDeriv μ ν x ∂ν := by
        rw [setLIntegral_measure_zero _ _ (measure_mono_null Set.inter_subset_left ?_),
          Set.inter_comm, zero_add]
        exact measure_singularPartSet _ _

lemma restrict_compl_singularPartSet_eq_withDensity
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.restrict (singularPartSet μ ν)ᶜ = ν.withDensity (μ.rnDeriv ν) := by
  ext t ht
  rw [restrict_apply ht, measure_inter_compl_singularPartSet μ ν ht, withDensity_apply _ ht]

lemma restrict_singularPartSet_eq_singularPart (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.restrict (singularPartSet μ ν) = μ.singularPart ν := by
  have h_add := haveLebesgueDecomposition_add μ ν
  rw [← restrict_compl_singularPartSet_eq_withDensity μ ν] at h_add
  have : μ = μ.restrict (singularPartSet μ ν) + μ.restrict (singularPartSet μ ν)ᶜ := by
    rw [restrict_add_restrict_compl measurableSet_singularPartSet]
  conv_lhs at h_add => rw [this]
  exact (Measure.add_left_inj _ _ _).mp h_add

lemma absolutelyContinuous_restrict_compl_singularPartSet
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.restrict (singularPartSet μ ν)ᶜ ≪ ν := by
  rw [restrict_compl_singularPartSet_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

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

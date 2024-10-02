/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.fDivStatInfo

/-!

# Test: alternative f-divergence definition

-/

open Real MeasureTheory Filter Set MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {f g : ℝ → ℝ}

noncomputable
def rightLimZero (f : ℝ → ℝ) : EReal := (fun x ↦ (f x : EReal)).rightLim 0

lemma rightLimZero_of_tendsto (h : Tendsto f (𝓝[>] 0) (𝓝 (f 0))) :
    rightLimZero f = f 0 := rightLim_eq_of_tendsto NeBot.ne' (EReal.tendsto_coe.mpr h)

lemma rightLimZero_of_tendsto_atTop (h : Tendsto f (𝓝[>] 0) atTop) :
    rightLimZero f = ⊤ := by
  refine rightLim_eq_of_tendsto NeBot.ne' ?_
  rw [EReal.tendsto_nhds_top_iff_real]
  rw [tendsto_atTop] at h
  intro x
  filter_upwards [h (x + 1)] with y hy
  norm_cast
  exact (lt_add_one x).trans_le hy

open Classical in
/-- f-Divergence of two measures. -/
noncomputable
def fDiv' (f : ℝ → ℝ) (μ ν : Measure α) : EReal :=
  if ¬ IntegrableOn (fun x ↦ f (μ.rnDeriv ν x).toReal) (ν.singularPartSet μ)ᶜ ν then ⊤
  else ∫ x in (ν.singularPartSet μ)ᶜ, f (μ.rnDeriv ν x).toReal ∂ν
    + derivAtTop f * μ.singularPart ν .univ + rightLimZero f * ν.singularPart μ univ

lemma integrableOn_f_rnDeriv_singularPartSet_iff [SigmaFinite μ] [SigmaFinite ν] :
    IntegrableOn (fun x ↦ f (μ.rnDeriv ν x).toReal) (ν.singularPartSet μ) ν
      ↔ f 0 = 0 ∨ ν (ν.singularPartSet μ) < ⊤ := by
  have h := Measure.rnDeriv_eq_zero_ae_of_singularPartSet ν μ ν
  have h' : ∀ᵐ (x : α) ∂ν, x ∈ ν.singularPartSet μ → f ((∂μ/∂ν) x).toReal = f 0 := by
    filter_upwards [h] with x hx h_mem
    rw [hx h_mem, ENNReal.zero_toReal]
  rw [← ae_restrict_iff' Measure.measurableSet_singularPartSet] at h'
  rw [integrableOn_congr_fun_ae h']
  by_cases h0 : f 0 = 0 <;> simp [h0]

lemma integrableOn_and_compl [NormedAddCommGroup β] {f : α → β} (s : Set α) {μ : Measure α} :
    IntegrableOn f s μ ∧ IntegrableOn f sᶜ μ ↔ Integrable f μ := by
  rw [← integrableOn_union, ← integrableOn_univ, union_compl_self]

lemma fDiv'_eq_fDiv [SigmaFinite μ] [SigmaFinite ν] (hfc : ContinuousOn f (Ici 0)) :
    fDiv' f μ ν = fDiv f μ ν := by
  have h_zero : rightLimZero f = f 0 := by
    refine rightLimZero_of_tendsto ?_
    have h_tendsto_ge : Tendsto f (𝓝[≥] 0) (𝓝 (f 0)) := (hfc 0 (mem_Ici.mpr le_rfl)).tendsto
    exact tendsto_nhdsWithin_mono_left (Ioi_subset_Ici le_rfl) h_tendsto_ge
  by_cases h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν
  swap
  · rw [fDiv_of_not_integrable h_int, fDiv']
    rw [← integrableOn_and_compl (ν.singularPartSet μ)] at h_int
    split_ifs with h
    · rw [integrableOn_f_rnDeriv_singularPartSet_iff] at h_int
      simp only [h, and_true, not_or, not_lt, top_le_iff] at h_int
      rw [← Measure.measure_singularPartSet' ν μ, h_int.2, EReal.coe_ennreal_top]
      rw [h_zero, EReal.coe_mul_top_of_pos]
      swap; · sorry
      rw [EReal.add_top_of_ne_bot]
      simp only [ne_eq, EReal.add_eq_bot_iff, EReal.coe_ne_bot, false_or]
      rw [EReal.mul_eq_bot]
      simp only [EReal.coe_ennreal_pos, Measure.measure_univ_pos, ne_eq, EReal.coe_ennreal_ne_bot,
        and_false, EReal.coe_ennreal_eq_top_iff, false_or, not_or, not_and, not_not, not_lt]
      sorry
    · rfl
  rw [fDiv', if_neg, h_zero]
  swap; · push_neg; exact h_int.integrableOn
  rw [fDiv_of_integrable h_int]
  suffices ((∫ x, f ((∂μ/∂ν) x).toReal ∂ν : ℝ) : EReal)
      = ∫ x in (ν.singularPartSet μ)ᶜ, f (μ.rnDeriv ν x).toReal ∂ν
        + f 0 * ν.singularPart μ .univ by
    rw [this, add_assoc, add_assoc]
    congr 1
    rw [add_comm]
  rw [← integral_add_compl (Measure.measurableSet_singularPartSet (μ := ν) (ν := μ)) h_int,
    add_comm, EReal.coe_add]
  congr
  have h := Measure.rnDeriv_eq_zero_ae_of_singularPartSet ν μ ν
  have h' : ∀ᵐ (x : α) ∂ν, x ∈ ν.singularPartSet μ → f ((∂μ/∂ν) x).toReal = f 0 := by
    filter_upwards [h] with x hx h_mem
    rw [hx h_mem, ENNReal.zero_toReal]
  rw [← Measure.measure_singularPartSet' ν μ,
    setIntegral_congr_ae Measure.measurableSet_singularPartSet h']
  simp only [integral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, smul_eq_mul,
    EReal.coe_mul]
  rw [mul_comm]
  by_cases h0 : f 0 = 0
  · simp [h0]
  congr
  refine EReal.coe_ennreal_toReal ?_
  have h_int' : IntegrableOn (fun x ↦ f (μ.rnDeriv ν x).toReal) (ν.singularPartSet μ) ν :=
    h_int.integrableOn
  rw [← ae_restrict_iff' Measure.measurableSet_singularPartSet] at h'
  rw [integrableOn_congr_fun_ae h'] at h_int'
  simp only [integrableOn_const, h0, false_or] at h_int'
  exact h_int'.ne

end ProbabilityTheory

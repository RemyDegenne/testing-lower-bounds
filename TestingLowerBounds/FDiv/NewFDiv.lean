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
def rightLimZero (f : ℝ → ℝ) : EReal := Function.rightLim (fun x ↦ (f x : EReal)) (0 : ℝ)

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
  if ¬ Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν then ⊤
  else ∫ x in (ν.singularPartSet μ)ᶜ, f (μ.rnDeriv ν x).toReal ∂ν
    + derivAtTop f * μ.singularPart ν .univ + rightLimZero f * ν.singularPart μ univ

lemma fDiv'_eq_fDiv [SigmaFinite μ] [IsFiniteMeasure ν] (hfc : ContinuousOn f (Ici 0)) :
    fDiv' f μ ν = fDiv f μ ν := by
  by_cases h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν
  swap; · rw [fDiv_of_not_integrable h_int, fDiv', if_pos h_int]
  have h_zero : rightLimZero f = f 0 := by
    refine rightLimZero_of_tendsto ?_
    have h_tendsto_ge : Tendsto f (𝓝[≥] 0) (𝓝 (f 0)) := (hfc 0 (mem_Ici.mpr le_rfl)).tendsto
    exact tendsto_nhdsWithin_mono_left (Ioi_subset_Ici le_rfl) h_tendsto_ge
  rw [fDiv', if_neg, h_zero]
  swap; · simp [h_int]
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
  rw [← Measure.measure_singularPartSet' ν μ]
  have : ∫ x in ν.singularPartSet μ, f ((∂μ/∂ν) x).toReal ∂ν
      = ∫ _ in ν.singularPartSet μ, f 0 ∂ν := by
    refine setIntegral_congr_ae Measure.measurableSet_singularPartSet ?_
    filter_upwards [h] with x hx h_mem
    rw [hx h_mem, ENNReal.zero_toReal]
  rw [this]
  simp only [integral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, smul_eq_mul,
    EReal.coe_mul]
  rw [mul_comm]
  congr
  refine EReal.coe_ennreal_toReal ?_
  simp

end ProbabilityTheory

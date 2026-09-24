/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import TestingLowerBounds.Divergences.KullbackLeibler.KLDivFun
public import TestingLowerBounds.FDiv.Basic
public import TestingLowerBounds.FDiv.DPIJensen
public import TestingLowerBounds.FDiv.Measurable

/-!
# Kullback-Leibler divergence

The Kullback-Leibler divergence `klDiv` is defined in Mathlib (`InformationTheory.klDiv`).
This file relates it to the f-divergence for the divergence function `klDivFun`.

## Main statements

* `klDiv_eq_fDiv`: `klDiv μ ν = fDiv klDivFun μ ν`
* `klDiv_fst_le`, `klDiv_snd_le`, `le_klDiv_compProd`, `klDiv_comp_le_compProd`: data-processing
  inequalities, from Mathlib's `klDiv_map_le`.

-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace Set InformationTheory

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

lemma klDiv_eq_fDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = fDiv klDivFun μ ν := by
  classical
  rw [klDiv_eq_lintegral_klFun, fDiv_of_derivAtTop_eq_top derivAtTop_klDivFun,
    lintegral_klDivFun_rnDeriv]

lemma measurable_klDiv {β : Type*} [MeasurableSpace β] [CountableOrCountablyGenerated α β]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦ klDiv (κ a) (η a)) := by
  simp_rw [klDiv_eq_fDiv]
  exact measurable_fDiv _ _

section Scaling

/-! ### Scaling of the measures -/

lemma klDiv_smul_left_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : ℝ≥0∞}
    (hc : c ≠ 0) (hc_top : c ≠ ∞) :
    klDiv (c • μ) ν = ∞ ↔ klDiv μ ν = ∞ := by
  rw [klDiv_eq_top_iff, klDiv_eq_top_iff]
  have h_ac : c • μ ≪ ν ↔ μ ≪ ν :=
    ⟨fun h ↦ (Measure.absolutelyContinuous_smul hc).trans h, fun h ↦ h.smul_left c⟩
  rw [h_ac]
  refine imp_congr_right fun hμν ↦ not_congr ?_
  rw [integrable_smul_measure hc hc_top, integrable_congr (llr_smul_left hμν c hc hc_top),
    integrable_add_iff_integrable_left' (integrable_const _)]

lemma klDiv_smul_left_eq_ofReal [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : klDiv μ ν ≠ ∞)
    {c : ℝ≥0∞} (hc_top : c ≠ ∞) :
    klDiv (c • μ) ν = ENNReal.ofReal (c.toReal * (klDiv μ ν).toReal
      + (1 - c.toReal) * (ν .univ).toReal + c.toReal * log c.toReal * (μ .univ).toReal) := by
  by_cases hc : c = 0
  · simp [hc, klDiv_zero_left]
  have h' : klDiv (c • μ) ν ≠ ∞ := by rwa [ne_eq, klDiv_smul_left_eq_top_iff hc hc_top]
  rw [klDiv_ne_top_iff] at h
  lift c to ℝ≥0 using hc_top
  rw [← ENNReal.smul_def] at h' ⊢
  rw [← ENNReal.ofReal_toReal h', toReal_klDiv_smul_left h.1 h.2 c, ENNReal.coe_toReal,
    measureReal_def, measureReal_def]

lemma klDiv_smul_right_eq_smul_left' [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : ℝ≥0∞}
    (hc : c ≠ 0) (hc_top : c ≠ ∞) :
    klDiv μ (c • ν) = c * klDiv (c⁻¹ • μ) ν := by
  lift c to ℝ≥0 using hc_top
  have hc' : c ≠ 0 := by simpa using hc
  rw [← ENNReal.smul_def, ← ENNReal.coe_inv hc', ← ENNReal.smul_def]
  exact klDiv_smul_right_eq_smul_left hc'

lemma klDiv_smul_right_eq_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : ℝ≥0∞}
    (hc : c ≠ 0) (hc_top : c ≠ ∞) :
    klDiv μ (c • ν) = ∞ ↔ klDiv μ ν = ∞ := by
  rw [klDiv_smul_right_eq_smul_left' hc hc_top, ENNReal.mul_eq_top,
    klDiv_smul_left_eq_top_iff (ENNReal.inv_ne_zero.mpr hc_top) (ENNReal.inv_ne_top.mpr hc)]
  simp [hc, hc_top]

lemma klDiv_smul_same' [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : ℝ≥0∞} (hc_top : c ≠ ∞) :
    klDiv (c • μ) (c • ν) = c * klDiv μ ν := by
  lift c to ℝ≥0 using hc_top
  rw [← ENNReal.smul_def, ← ENNReal.smul_def]
  exact klDiv_smul_same c

lemma klDiv_smul_left_le_of_le {β : Type*} {mβ : MeasurableSpace β} {μ₁ ν₁ : Measure α}
    {μ₂ ν₂ : Measure β} [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν₂] (h_eq_μ : μ₁ .univ = μ₂ .univ) (h_eq_ν : ν₁ .univ = ν₂ .univ)
    (h_le : klDiv μ₁ ν₁ ≤ klDiv μ₂ ν₂) {c : ℝ≥0∞} (hc_top : c ≠ ∞) :
    klDiv (c • μ₁) ν₁ ≤ klDiv (c • μ₂) ν₂ := by
  by_cases h2 : klDiv μ₂ ν₂ = ∞
  · by_cases hc : c = 0
    · simp [hc, klDiv_zero_left, h_eq_ν]
    · rw [(klDiv_smul_left_eq_top_iff hc hc_top).mpr h2]
      exact le_top
  have h1 : klDiv μ₁ ν₁ ≠ ∞ := ne_top_of_le_ne_top h2 h_le
  rw [klDiv_smul_left_eq_ofReal h1 hc_top, klDiv_smul_left_eq_ofReal h2 hc_top, h_eq_μ, h_eq_ν]
  gcongr

lemma klDiv_smul_smul_le_of_le {β : Type*} {mβ : MeasurableSpace β} {μ₁ ν₁ : Measure α}
    {μ₂ ν₂ : Measure β} [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν₂] (h_eq_μ : μ₁ .univ = μ₂ .univ) (h_eq_ν : ν₁ .univ = ν₂ .univ)
    (h_le : klDiv μ₁ ν₁ ≤ klDiv μ₂ ν₂) {c c' : ℝ≥0∞} (hc_top : c ≠ ∞) (hc' : c' ≠ 0)
    (hc'_top : c' ≠ ∞) :
    klDiv (c • μ₁) (c' • ν₁) ≤ klDiv (c • μ₂) (c' • ν₂) := by
  lift c to ℝ≥0 using hc_top
  lift c' to ℝ≥0 using hc'_top
  have hc'0 : c' ≠ 0 := by simpa using hc'
  have h := klDiv_smul_left_le_of_le h_eq_μ h_eq_ν h_le (c := ((c'⁻¹ * c : ℝ≥0) : ℝ≥0∞))
    ENNReal.coe_ne_top
  rw [← ENNReal.smul_def, ← ENNReal.smul_def] at h
  rw [← ENNReal.smul_def, ← ENNReal.smul_def, ← ENNReal.smul_def, ← ENNReal.smul_def,
    klDiv_smul_right_eq_smul_left hc'0, klDiv_smul_right_eq_smul_left hc'0, smul_smul, smul_smul]
  gcongr

/-- Monotonicity of the Kullback-Leibler divergence of the normalized measures, for fixed
masses. -/
lemma klDiv_inv_smul_le_of_le {β : Type*} {mβ : MeasurableSpace β} {μ₁ ν₁ : Measure α}
    {μ₂ ν₂ : Measure β} [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν₂] (h_eq_μ : μ₁ .univ = μ₂ .univ) (h_eq_ν : ν₁ .univ = ν₂ .univ)
    (h_le : klDiv μ₁ ν₁ ≤ klDiv μ₂ ν₂) :
    klDiv ((μ₁ .univ)⁻¹ • μ₁) ((ν₁ .univ)⁻¹ • ν₁)
      ≤ klDiv ((μ₂ .univ)⁻¹ • μ₂) ((ν₂ .univ)⁻¹ • ν₂) := by
  by_cases hν : ν₂ .univ = 0
  · have hν₁ : ν₁ .univ = 0 := h_eq_ν.trans hν
    obtain rfl := Measure.measure_univ_eq_zero.mp hν
    obtain rfl := Measure.measure_univ_eq_zero.mp hν₁
    simp only [Measure.coe_zero, Pi.zero_apply, ENNReal.inv_zero, smul_zero]
    by_cases hμ : μ₂ = 0
    · subst hμ
      obtain rfl : μ₁ = 0 := Measure.measure_univ_eq_zero.mp (h_eq_μ.trans (by simp))
      simp
    · have : NeZero μ₂ := ⟨hμ⟩
      rw [klDiv_zero_right (μ := (μ₂ .univ)⁻¹ • μ₂)]
      exact le_top
  have : NeZero ν₂ := ⟨fun h ↦ hν (by simp [h])⟩
  have : NeZero ν₁ := ⟨fun h ↦ hν (h_eq_ν.symm.trans (by simp [h]))⟩
  by_cases hμ : μ₂ .univ = 0
  · have hμ₁ : μ₁ .univ = 0 := h_eq_μ.trans hμ
    obtain rfl := Measure.measure_univ_eq_zero.mp hμ
    obtain rfl := Measure.measure_univ_eq_zero.mp hμ₁
    simp only [smul_zero, klDiv_zero_left, measure_univ, le_refl]
  rw [h_eq_μ, h_eq_ν]
  exact klDiv_smul_smul_le_of_le h_eq_μ h_eq_ν h_le (ENNReal.inv_ne_top.mpr hμ)
    (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (ENNReal.inv_ne_top.mpr hν)

end Scaling

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β}

lemma klDiv_fst_le (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ.fst ν.fst ≤ klDiv μ ν :=
  klDiv_map_le μ ν measurable_fst

lemma klDiv_snd_le (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ.snd ν.snd ≤ klDiv μ ν :=
  klDiv_map_le μ ν measurable_snd

lemma le_klDiv_compProd (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv μ ν ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simpa using klDiv_fst_le (μ ⊗ₘ κ) (ν ⊗ₘ η)

lemma klDiv_comp_le_compProd (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (κ ∘ₘ μ) (η ∘ₘ ν) ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simpa using klDiv_snd_le (μ ⊗ₘ κ) (ν ⊗ₘ η)

end DataProcessingInequality

end ProbabilityTheory

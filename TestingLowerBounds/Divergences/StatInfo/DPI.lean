/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.StatInfo.fDivStatInfo

/-!
# fDiv and StatInfo

-/

open MeasureTheory Set

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {f : ℝ → ℝ} {β γ x t : ℝ}

/-- **Data processing inequality** for the f-divergence of `statInfoFun`. -/
lemma fDiv_statInfoFun_comp_right_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] (hβ : 0 ≤ β) :
    fDiv (statInfoFun β γ) (η ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv (statInfoFun β γ) μ ν := by
  rcases le_total γ 0 with (hγ | hγ)
  · rw [fDiv_statInfoFun_eq_zero_of_nonneg_of_nonpos hβ hγ,
      fDiv_statInfoFun_eq_zero_of_nonneg_of_nonpos hβ hγ]
  simp_rw [fDiv_statInfoFun_eq_StatInfo_of_nonneg hβ hγ]
  gcongr ?_ + ?_
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr <| statInfo_comp_le _ _ _ _
  · simp_rw [Measure.comp_apply_univ, le_refl]

-- The name is `fDiv_comp_right_le'`, since there is already `fDiv_comp_right_le`
-- in the `fDiv.CompProd` file.
/-- **Data processing inequality** for the f-divergence. -/
theorem fDiv_comp_right_le' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    fDiv f (η ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv f μ ν := by
  simp_rw [fDiv_eq_lintegral_fDiv_statInfoFun hf_cvx hf_cont, Measure.comp_apply_univ]
  gcongr
  simp only [EReal.coe_ennreal_le_coe_ennreal_iff]
  exact lintegral_mono fun x ↦ EReal.toENNReal_le_toENNReal <|
    fDiv_statInfoFun_comp_right_le η zero_le_one

lemma fDiv_fst_le' (μ ν : Measure (𝒳 × 𝒳')) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    fDiv f μ.fst ν.fst ≤ fDiv f μ ν := by
  simp_rw [Measure.fst, ← Measure.comp_deterministic_eq_map measurable_fst]
  exact fDiv_comp_right_le' _ hf_cvx hf_cont

lemma fDiv_snd_le' (μ ν : Measure (𝒳 × 𝒳')) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    fDiv f μ.snd ν.snd ≤ fDiv f μ ν := by
  simp_rw [Measure.snd, ← Measure.comp_deterministic_eq_map measurable_snd]
  exact fDiv_comp_right_le' _ hf_cvx hf_cont

lemma le_fDiv_compProd' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel 𝒳 𝒳') [IsMarkovKernel κ] [IsMarkovKernel η] (hf_cvx : ConvexOn ℝ univ f)
    (hf_cont : Continuous f) :
    fDiv f μ ν ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  nth_rw 1 [← Measure.fst_compProd μ κ, ← Measure.fst_compProd ν η]
  exact fDiv_fst_le' _ _ hf_cvx hf_cont

lemma fDiv_compProd_right' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel 𝒳 𝒳') [IsMarkovKernel κ] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = fDiv f μ ν := by
  refine le_antisymm ?_ (le_fDiv_compProd' κ κ hf_cvx hf_cont)
  simp_rw [Measure.compProd_eq_comp]
  exact fDiv_comp_right_le' _ hf_cvx hf_cont

lemma fDiv_comp_le_compProd' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel 𝒳 𝒳') [IsMarkovKernel κ] [IsMarkovKernel η] (hf_cvx : ConvexOn ℝ univ f)
    (hf_cont : Continuous f) :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  nth_rw 1 [← Measure.snd_compProd μ κ, ← Measure.snd_compProd ν η]
  exact fDiv_snd_le' _ _ hf_cvx hf_cont

lemma fDiv_comp_le_compProd_right' [IsFiniteMeasure μ]
    (κ η : Kernel 𝒳 𝒳') [IsMarkovKernel κ] [IsMarkovKernel η] (hf_cvx : ConvexOn ℝ univ f)
    (hf_cont : Continuous f) :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ μ) ≤ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) :=
  fDiv_comp_le_compProd' κ η hf_cvx hf_cont

end ProbabilityTheory

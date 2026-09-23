/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.FDiv.FDivEqIntegral

/-!
# fDiv and StatInfo

-/

open MeasureTheory Set

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {f : DivFunction} {β γ x t : ℝ}

lemma toReal_fDiv_statInfoFun_comp_right_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] (hβ : 0 ≤ β) :
    (fDiv (statInfoDivFun β γ) (η ∘ₘ μ) (η ∘ₘ ν)).toReal
      ≤ (fDiv (statInfoDivFun β γ) μ ν).toReal := by
  rcases le_total γ 0 with (hγ | hγ)
  · rw [fDiv_statInfoFun_eq_zero_of_nonneg_of_nonpos hβ hγ,
      fDiv_statInfoFun_eq_zero_of_nonneg_of_nonpos hβ hγ]
  simp_rw [fDiv_statInfoFun_eq_StatInfo_of_nonneg hβ hγ]
  gcongr ?_ + ?_
  · rw [ENNReal.toReal_le_toReal statInfo_ne_top statInfo_ne_top]
    exact statInfo_comp_le _ _ _ _
  · simp_rw [Measure.comp_apply_univ, le_refl]

/-- **Data processing inequality** for the f-divergence of `statInfoFun`. -/
lemma fDiv_statInfoFun_comp_right_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] (hβ : 0 ≤ β) :
    fDiv (statInfoDivFun β γ) (η ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv (statInfoDivFun β γ) μ ν := by
  rw [← ENNReal.toReal_le_toReal fDiv_statInfoDivFun_ne_top fDiv_statInfoDivFun_ne_top]
  exact toReal_fDiv_statInfoFun_comp_right_le η hβ

-- The name is `fDiv_comp_right_le'`, since there is already `fDiv_comp_right_le`
-- in the `fDiv.CompProd` file.
/-- **Data processing inequality** for the f-divergence. -/
theorem fDiv_comp_right_le' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (η : Kernel 𝒳 𝒳') [IsMarkovKernel η] :
    fDiv f (η ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv f μ ν := by
  have h1 := fDiv_eq_lintegral_fDiv_statInfoFun (f := f) (μ := η ∘ₘ μ) (ν := η ∘ₘ ν)
  have h2 := fDiv_eq_lintegral_fDiv_statInfoFun (f := f) (μ := μ) (ν := ν)
  rw [Measure.comp_apply_univ, Measure.comp_apply_univ] at h1
  have h3 : fDiv f (η ∘ₘ μ) (η ∘ₘ ν) + ENNReal.ofReal (rightDeriv f.realFun 1) * ν univ
      ≤ fDiv f μ ν + ENNReal.ofReal (rightDeriv f.realFun 1) * ν univ := by
    rw [h1, h2]
    exact add_le_add
      (lintegral_mono fun x ↦ fDiv_statInfoFun_comp_right_le (μ := μ) (ν := ν) η zero_le_one) le_rfl
  exact (ENNReal.add_le_add_iff_right
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _))).mp h3

lemma fDiv_fst_le' (μ ν : Measure (𝒳 × 𝒳')) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ.fst ν.fst ≤ fDiv f μ ν := by
  simp_rw [Measure.fst, ← Measure.deterministic_comp_eq_map measurable_fst]
  exact fDiv_comp_right_le' _

lemma fDiv_snd_le' (μ ν : Measure (𝒳 × 𝒳')) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ.snd ν.snd ≤ fDiv f μ ν := by
  simp_rw [Measure.snd, ← Measure.deterministic_comp_eq_map measurable_snd]
  exact fDiv_comp_right_le' _

lemma le_fDiv_compProd' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel 𝒳 𝒳') [IsMarkovKernel κ] [IsMarkovKernel η] :
    fDiv f μ ν ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  nth_rw 1 [← Measure.fst_compProd μ κ, ← Measure.fst_compProd ν η]
  exact fDiv_fst_le' _ _

lemma fDiv_compProd_right' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel 𝒳 𝒳') [IsMarkovKernel κ] :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = fDiv f μ ν := by
  refine le_antisymm ?_ (le_fDiv_compProd' κ κ)
  simp_rw [Measure.compProd_eq_comp_prod]
  exact fDiv_comp_right_le' _

lemma fDiv_comp_le_compProd' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel 𝒳 𝒳') [IsMarkovKernel κ] [IsMarkovKernel η] :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  nth_rw 1 [← Measure.snd_compProd μ κ, ← Measure.snd_compProd ν η]
  exact fDiv_snd_le' _ _

lemma fDiv_comp_le_compProd_right' [IsFiniteMeasure μ]
    (κ η : Kernel 𝒳 𝒳') [IsMarkovKernel κ] [IsMarkovKernel η] :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ μ) ≤ fDiv f (μ ⊗ₘ κ) (μ ⊗ₘ η) :=
  fDiv_comp_le_compProd' κ η

end ProbabilityTheory

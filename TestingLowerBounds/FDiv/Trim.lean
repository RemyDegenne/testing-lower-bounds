/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.FDiv.Basic

/-!

# f-Divergences on sub-sigma-algebras

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open Real MeasureTheory Filter Set

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {f g : ℝ → ℝ}

lemma f_condexp_rnDeriv_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    (fun x ↦ f ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | m]) x))
      ≤ᵐ[ν.trim hm] ν[fun x ↦ f ((∂μ/∂ν) x).toReal | m] := by
  sorry -- Jensen for condexp. We don't have it yet.

lemma f_rnDeriv_trim_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    (fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x).toReal)
      ≤ᵐ[ν.trim hm] ν[fun x ↦ f ((∂μ/∂ν) x).toReal | m] := by
  filter_upwards [Measure.toReal_rnDeriv_trim_of_ac hm hμν,
    f_condexp_rnDeriv_le hm hf hf_cvx hf_cont h_int] with a ha1 ha2
  calc f ((∂μ.trim hm/∂ν.trim hm) a).toReal
      = f ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | m]) a) := by rw [ha1]
    _ ≤ (ν[fun x ↦ f ((∂μ/∂ν) x).toReal | m]) a := ha2

lemma integrable_f_rnDeriv_trim [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    Integrable (fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x).toReal) (ν.trim hm) := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x).toReal)
    (g₁ := fun x ↦ c * ((∂μ.trim hm/∂ν.trim hm) x).toReal + c')
    (g₂ := fun x ↦ (ν[fun x ↦ f ((∂μ/∂ν) x).toReal | m]) x)
    ?_ ?_ ?_ ?_ ?_
  · refine (hf.comp_measurable ?_).aestronglyMeasurable
    exact @Measurable.ennreal_toReal _ m _ (Measure.measurable_rnDeriv _ _)
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_trim_le hm hμν hf hf_cvx hf_cont h_int
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    exact Measure.integrable_toReal_rnDeriv
  · exact integrable_condexp.trim hm stronglyMeasurable_condexp

lemma integrable_f_condexp_rnDeriv [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : m ≤ mα) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    Integrable (fun x ↦ f ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | m]) x)) ν := by
  have h := integrable_f_rnDeriv_trim hm hμν hf hf_cvx hf_cont h_int
  refine integrable_of_integrable_trim hm ((integrable_congr ?_).mp h)
  filter_upwards [Measure.toReal_rnDeriv_trim_of_ac hm hμν] with a ha
  rw [ha]

lemma fDiv_trim_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f (μ.trim hm) (ν.trim hm) = ∫ x, f ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | m]) x) ∂ν := by
  classical
  rw [fDiv_of_absolutelyContinuous (hμν.trim hm),
    if_pos (integrable_f_rnDeriv_trim hm hμν hf hf_cvx hf_cont h_int)]
  congr 1
  rw [integral_trim hm]
  swap; · exact hf.comp_measurable stronglyMeasurable_condexp.measurable
  refine integral_congr_ae ?_
  filter_upwards [Measure.toReal_rnDeriv_trim_of_ac hm hμν] with a ha
  rw [ha]

lemma fDiv_trim_le_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) :
    fDiv f (μ.trim hm) (ν.trim hm) ≤ fDiv f μ ν := by
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  swap; · rw [fDiv_of_not_integrable h_int]; exact le_top
  rw [fDiv_trim_of_ac hm hμν hf hf_cvx hf_cont h_int]
  classical
  rw [fDiv_of_absolutelyContinuous hμν, if_pos h_int]
  norm_cast
  conv_rhs => rw [← integral_condexp hm]
  refine integral_mono_ae (integrable_f_condexp_rnDeriv hm hμν hf hf_cvx hf_cont h_int) ?_ ?_
  · exact integrable_condexp
  refine ae_of_ae_trim hm ?_
  exact f_condexp_rnDeriv_le hm hf hf_cvx hf_cont h_int

lemma fDiv_trim_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) :
    fDiv f (μ.trim hm) (ν.trim hm) ≤ fDiv f μ ν := by
  have h1 : μ.trim hm = (ν.withDensity (∂μ/∂ν)).trim hm + (μ.singularPart ν).trim hm := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm, trim_add]
  rw [h1, fDiv_eq_add_withDensity_derivAtTop μ ν hf_cvx]
  refine (fDiv_add_measure_le _ _ _ hf hf_cvx).trans ?_
  refine add_le_add ?_ ?_
  · exact fDiv_trim_le_of_ac hm (withDensity_absolutelyContinuous ν (∂μ/∂ν)) hf hf_cvx hf_cont
  · rw [trim_measurableSet_eq hm MeasurableSet.univ]

end ProbabilityTheory

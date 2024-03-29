/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.FDiv.Basic
import TestingLowerBounds.MeasureCompProd

/-!

# f-Divergences on sub-sigma-algebras

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open Real MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {f g : ℝ → ℝ}

lemma f_condexp_rnDeriv_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    (fun x ↦ f ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | m]) x))
      ≤ᵐ[ν.trim hm] ν[fun x ↦ f ((∂μ/∂ν) x).toReal | m] := by
  sorry -- Jensen for condexp. We don't have it yet.

lemma f_rnDeriv_trim_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
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
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
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
  · exact @ae_of_all _ m _ _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact f_rnDeriv_trim_le hm hμν hf hf_cvx hf_cont h_int
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    exact Measure.integrable_toReal_rnDeriv
  · exact integrable_condexp.trim hm stronglyMeasurable_condexp

lemma integrable_f_condexp_rnDeriv [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : m ≤ mα) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    Integrable (fun x ↦ f ((ν[fun x ↦ ((∂μ/∂ν) x).toReal | m]) x)) ν := by
  have h := integrable_f_rnDeriv_trim hm hμν hf hf_cvx hf_cont h_int
  refine integrable_of_integrable_trim hm ((integrable_congr ?_).mp h)
  filter_upwards [Measure.toReal_rnDeriv_trim_of_ac hm hμν] with a ha
  rw [ha]

lemma fDiv_trim_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα) (hμν : μ ≪ ν)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
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
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) :
    fDiv f (μ.trim hm) (ν.trim hm) ≤ fDiv f μ ν := by
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  swap; · rw [fDiv_of_not_integrable h_int]; exact le_top
  rw [fDiv_trim_of_ac hm hμν hf hf_cvx hf_cont h_int]
  classical
  rw [fDiv_of_absolutelyContinuous hμν, if_pos h_int]
  norm_cast
  conv_rhs => rw [← integral_condexp hm h_int]
  refine integral_mono_ae (integrable_f_condexp_rnDeriv hm hμν hf hf_cvx hf_cont h_int) ?_ ?_
  · exact integrable_condexp
  refine ae_of_ae_trim hm ?_
  exact f_condexp_rnDeriv_le hm hf hf_cvx hf_cont h_int

lemma Measure.trim_add (μ ν : Measure α) (hm : m ≤ mα) :
    (μ + ν).trim hm = μ.trim hm + ν.trim hm := by
  refine @Measure.ext _ m _ _ (fun s hs ↦ ?_)
  simp only [Measure.add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply,
    trim_measurableSet_eq hm hs]

lemma fDiv_trim_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ mα)
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) :
    fDiv f (μ.trim hm) (ν.trim hm) ≤ fDiv f μ ν := by
  let μ' := μ.singularPart ν
  have h1 : μ.trim hm = (ν.withDensity (∂μ/∂ν)).trim hm
      + (ν.trim hm).withDensity (∂(μ'.trim hm)/∂(ν.trim hm))
      + (μ'.trim hm).singularPart (ν.trim hm) := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm, Measure.trim_add,
      ← Measure.rnDeriv_add_singularPart ((μ.singularPart ν).trim hm) (ν.trim hm), ← add_assoc]
  rw [h1, fDiv_absolutelyContinuous_add_mutuallySingular _
    (Measure.mutuallySingular_singularPart _ _) hf_cvx]
  swap
  · rw [Measure.AbsolutelyContinuous.add_left_iff]
    constructor
    · exact (withDensity_absolutelyContinuous _ _).trim hm
    · exact withDensity_absolutelyContinuous _ _
  calc fDiv f ((ν.withDensity (∂μ/∂ν)).trim hm + (ν.trim hm).withDensity (∂μ'.trim hm/∂ν.trim hm))
        (ν.trim hm)
      + derivAtTop f * (μ'.trim hm).singularPart (ν.trim hm) Set.univ
    ≤ fDiv f ((ν.withDensity (∂μ/∂ν)).trim hm) (ν.trim hm)
      + derivAtTop f * (ν.trim hm).withDensity (∂μ'.trim hm/∂ν.trim hm) Set.univ
      + derivAtTop f * (μ'.trim hm).singularPart (ν.trim hm) Set.univ := by
        gcongr
        refine fdiv_add_measure_le_of_ac ?_ ?_ hf hf_cvx
        · exact (withDensity_absolutelyContinuous _ _).trim hm
        · exact withDensity_absolutelyContinuous _ _
  _ = fDiv f ((ν.withDensity (∂μ/∂ν)).trim hm) (ν.trim hm)
      + derivAtTop f * ((ν.trim hm).withDensity (∂μ'.trim hm/∂ν.trim hm)
        + (μ'.trim hm).singularPart (ν.trim hm)) Set.univ := by
        simp only [Measure.add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply,
          EReal.coe_ennreal_add]
        rw [add_assoc]
        congr
        rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _),
          ← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_add]
        by_cases h_top : derivAtTop f = ⊤
        · rw [h_top]
          by_cases h01 : (ν.trim hm).withDensity (∂μ'.trim hm/∂ν.trim hm) Set.univ = 0
          · simp only [EReal.coe_add, h01, ENNReal.zero_toReal, EReal.coe_zero, mul_zero, zero_add]
          by_cases h02 : (μ'.trim hm).singularPart (ν.trim hm) Set.univ = 0
          · simp [h02]
          rw [EReal.top_mul_of_pos, EReal.top_mul_of_pos, EReal.top_mul_of_pos, EReal.top_add_top]
          · norm_cast
            exact add_pos (ENNReal.toReal_pos h01 (measure_ne_top _ _))
              (ENNReal.toReal_pos h02 (measure_ne_top _ _))
          · norm_cast
            exact ENNReal.toReal_pos h02 (measure_ne_top _ _)
          · norm_cast
            exact ENNReal.toReal_pos h01 (measure_ne_top _ _)
        lift derivAtTop f to ℝ using ⟨h_top, derivAtTop_ne_bot⟩ with df
        norm_cast
        rw [mul_add]
  _ = fDiv f ((ν.withDensity (∂μ/∂ν)).trim hm) (ν.trim hm)
      + derivAtTop f * μ'.trim hm Set.univ := by
        conv_rhs => rw [← Measure.rnDeriv_add_singularPart (μ'.trim hm) (ν.trim hm)]
  _ = fDiv f ((ν.withDensity (∂μ/∂ν)).trim hm) (ν.trim hm) + derivAtTop f * μ' Set.univ := by
        rw [trim_measurableSet_eq hm MeasurableSet.univ]
  _ ≤ fDiv f (ν.withDensity (∂μ/∂ν)) ν + derivAtTop f * μ' Set.univ := by
        gcongr
        exact fDiv_trim_le_of_ac hm (withDensity_absolutelyContinuous _ _) hf hf_cvx hf_cont
  _ = fDiv f μ ν := by conv_rhs => rw [fDiv_eq_add_withDensity_derivAtTop _ _ hf_cvx]

end ProbabilityTheory
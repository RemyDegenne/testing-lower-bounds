/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import TestingLowerBounds.FDiv.Basic
import TestingLowerBounds.FDiv.CompProd.EqTopIff
import TestingLowerBounds.FDiv.IntegralRnDerivSingularPart
import TestingLowerBounds.MeasureCompProd
/-!

# f-Divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

-/

open Real MeasureTheory Filter MeasurableSpace Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : ℝ → ℝ}

section Conditional

/-- Equivalence between two possible versions of the first condition for the finiteness of the
conditional f divergence, the second version is the preferred one.-/
lemma fDiv_ae_ne_top_iff [IsFiniteKernel κ] [IsFiniteKernel η] :
    (∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤)
    ↔ (∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
      ∧ (derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  simp_rw [fDiv_ne_top_iff, eventually_and, eventually_all]

/-- Equivalence between two possible versions of the second condition for the finiteness of the
conditional f divergence, the second version is the preferred one.-/
lemma integrable_fDiv_iff [CountableOrCountablyGenerated α β] [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η] (h_cvx : ConvexOn ℝ (Ici 0) f)
    (h_int : ∀ᵐ a ∂μ, Integrable (fun x ↦ f ((∂κ a/∂η a) x).toReal) (η a))
    (h_ac : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun x ↦ (fDiv f (κ x) (η x)).toReal) μ
      ↔ Integrable (fun a ↦ ∫ b, f ((∂κ a/∂η a) b).toReal ∂η a) μ := by
  have h_fin : ∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ⊤ := fDiv_ae_ne_top_iff.mpr ⟨h_int, h_ac⟩
  by_cases h_top : derivAtTop f = ⊤
  · classical
    simp_rw [fDiv_of_derivAtTop_eq_top h_top]
    simp only [fDiv_ne_top_iff, h_top, forall_true_left] at h_fin
    refine integrable_congr ?_
    filter_upwards [h_fin] with a ha
    rw [if_pos ha, EReal.toReal_coe]
  · have h_fin' := h_fin
    simp_rw [fDiv_ne_top_iff_of_derivAtTop_ne_top h_top] at h_fin
    have : (fun x ↦ (fDiv f (κ x) (η x)).toReal)
        =ᵐ[μ] (fun x ↦ ∫ y, f ((∂κ x/∂η x) y).toReal ∂(η x)
          + (derivAtTop f).toReal * ((κ x).singularPart (η x) .univ).toReal) := by
      filter_upwards [h_fin'] with x hx1
      rw [fDiv_of_ne_top hx1, EReal.toReal_add]
      · simp only [EReal.toReal_coe, add_right_inj]
        rw [EReal.toReal_mul]
        simp
      · simp
      · simp
      · simp [h_top, EReal.mul_eq_top, h_cvx.derivAtTop_ne_bot, measure_ne_top]
      · simp [EReal.mul_eq_bot, h_cvx.derivAtTop_ne_bot, h_top, measure_ne_top]
    rw [integrable_congr this]
    have h_int : Integrable (fun x ↦ (derivAtTop f).toReal
        * ((κ x).singularPart (η x) .univ).toReal) μ :=
      Integrable.const_mul integrable_singularPart (derivAtTop f).toReal
    have h_eq : (fun x ↦ ∫ y, f ((∂κ x/∂η x) y).toReal ∂η x)
        = (fun x ↦ (∫ y, f ((∂κ x/∂η x) y).toReal ∂η x +
          (derivAtTop f).toReal * ((κ x).singularPart (η x) .univ).toReal)
          - (derivAtTop f).toReal * ((κ x).singularPart (η x) .univ).toReal) := by
      ext; simp
    exact ⟨fun h ↦ h_eq ▸ h.sub h_int, fun h ↦ h.add h_int⟩

lemma fDiv_toReal_eq_ae {γ : Type*} [MeasurableSpace γ]
    {ξ : Kernel α β} {κ η : Kernel (α × β) γ} [IsFiniteKernel κ]
    (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (h_ac : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, κ (a, b) ≪ η (a, b))
    (h_int : ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a,
      Integrable (fun x ↦ f ((∂κ (a, b)/∂η (a, b)) x).toReal) (η (a, b))) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, (fDiv f (κ (a, b)) (η (a, b))).toReal =
      ∫ x, f ((∂κ (a, b)/∂η (a, b)) x).toReal ∂η (a, b)
      + (derivAtTop f).toReal * (((κ (a, b)).singularPart (η (a, b)) .univ)).toReal := by
  filter_upwards [eventually_all.mpr h_ac, h_int] with a ha_ae ha_int
  filter_upwards [eventually_all.mpr ha_ae, ha_int] with b hb_ae hb_int
  rw [← EReal.toReal_coe (∫ _, _ ∂_), fDiv_of_integrable hb_int, ← EReal.toReal_coe_ennreal,
    ← EReal.toReal_mul]
  refine EReal.toReal_add ?_ ?_ ?_ ?_
  · simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true]
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
  all_goals
  · by_cases h_deriv : derivAtTop f = ⊤
    · simp [Measure.singularPart_eq_zero_of_ac <| hb_ae h_deriv]
    · simp only [ne_eq, EReal.mul_eq_top, EReal.mul_eq_bot, hf_cvx.derivAtTop_ne_bot, false_and,
        EReal.coe_ennreal_ne_bot, and_false, h_deriv, EReal.coe_ennreal_pos,
        Measure.measure_univ_pos, ne_eq, EReal.coe_ennreal_eq_top_iff, false_or, not_and]
      exact fun _ ↦ measure_ne_top _ _

end Conditional

lemma integral_f_rnDeriv_mul_le_integral [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫ x, f ((∂μ/∂ν) x * κ x .univ).toReal ∂ν ≤ ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η) := by
  rw [Measure.integral_compProd h_int]
  refine integral_mono_ae ?_ ?_ ?_
  · exact integrable_f_rnDeriv_mul_kernel μ ν κ η hf hf_cvx hf_cont h_int hκη
  · rw [integrable_f_rnDeriv_compProd_iff hf hf_cvx] at h_int
    rw [integrable_congr (integral_f_compProd_congr _ _ _ _)]
    exact h_int.2
  · exact f_rnDeriv_ae_le_integral μ ν κ η hf_cvx hf_cont h_int hκη

lemma integral_f_rnDeriv_mul_withDensity_le_integral [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η)) :
    ∫ x, f ((∂μ/∂ν) x * η.withDensity (κ.rnDeriv η) x .univ).toReal ∂ν
      ≤ ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η) := by
  calc ∫ x, f ((∂μ/∂ν) x * η.withDensity (κ.rnDeriv η) x .univ).toReal ∂ν
    ≤ ∫ x, f ((∂μ ⊗ₘ (η.withDensity (κ.rnDeriv η))/∂ν ⊗ₘ η) x).toReal
      ∂(ν ⊗ₘ η) := by
        refine integral_f_rnDeriv_mul_le_integral μ ν (η.withDensity (κ.rnDeriv η))
          η hf hf_cvx hf_cont ?_ ?_
        · refine (integrable_congr ?_).mpr h_int
          filter_upwards [Measure.rnDeriv_measure_compProd_Kernel_withDensity μ ν κ η] with x hx
          rw [hx]
        · exact ae_of_all _ (fun _ ↦ Kernel.withDensity_absolutelyContinuous _ _)
  _ = ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η) := by
        refine integral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_measure_compProd_Kernel_withDensity μ ν κ η] with x hx
        rw [hx]

lemma integral_f_rnDeriv_le_integral_add [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (h_deriv : derivAtTop f = ⊤ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫ x, f ((∂μ/∂ν) x).toReal ∂ν
      ≤ ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η)
        + (derivAtTop f).toReal
          * ∫ a, ((∂μ/∂ν) a).toReal * (κ.singularPart η a .univ).toReal ∂ν := by
  suffices ∫ x, f ((∂μ/∂ν) x).toReal ∂ν
      ≤ ∫ x, f ((∂μ/∂ν) x * η.withDensity (κ.rnDeriv η) x .univ).toReal ∂ν
        + (derivAtTop f).toReal * ∫ a, ((∂μ/∂ν) a).toReal * (κ.singularPart η a .univ).toReal ∂ν by
    refine this.trans ?_
    gcongr
    exact integral_f_rnDeriv_mul_withDensity_le_integral μ ν κ η hf hf_cvx hf_cont h_int
  let κ' := η.withDensity (κ.rnDeriv η)
  have h : ∀ᵐ a ∂ν, f ((∂μ/∂ν) a).toReal
      ≤ f ((∂μ/∂ν) a * κ' a .univ).toReal
        + (derivAtTop f).toReal * ((∂μ/∂ν) a).toReal * (κ.singularPart η a .univ).toReal :=
    f_rnDeriv_le_add _ _ _ _ hf_cvx h_deriv
  have h_int_mul : Integrable (fun a ↦ f ((∂μ/∂ν) a * κ' a .univ).toReal) ν :=
    integrable_f_rnDeriv_mul_withDensity μ ν κ η hf hf_cvx hf_cont h_int
  have h_int_right : Integrable (fun a ↦ (derivAtTop f).toReal
      * ((∂μ/∂ν) a).toReal * (κ.singularPart η a .univ).toReal) ν := by
    simp_rw [mul_assoc]
    refine Integrable.const_mul ?_ _
    simp_rw [Kernel.singularPart_eq_singularPart_measure]
    exact integrable_rnDeriv_mul_singularPart _ _ _ _
  refine (integral_mono_ae ?_ ?_ h).trans_eq ?_
  · exact integrable_f_rnDeriv_of_integrable_compProd' μ ν κ η hf hf_cvx hf_cont h_int h_deriv
  · exact h_int_mul.add h_int_right
  rw [integral_add h_int_mul h_int_right]
  unfold_let κ'
  simp_rw [mul_assoc]
  rw [integral_mul_left]

lemma le_fDiv_compProd [CountableOrCountablyGenerated α β] (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousOn f (Ici 0)) :
    fDiv f μ ν ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  by_cases h_top : fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) = ⊤
  · simp [h_top]
  rw [fDiv_of_ne_top (fDiv_ne_top_of_fDiv_compProd_ne_top μ ν κ η hf hf_cvx hf_cont h_top),
    fDiv_of_ne_top h_top]
  obtain h_int := (fDiv_ne_top_iff.mp h_top).1
  rw [← ne_eq, fDiv_compProd_ne_top_iff hf hf_cvx] at h_top
  obtain ⟨_, _, h3⟩ := h_top
  calc ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν .univ
    ≤ ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η)
      + (derivAtTop f).toReal * ∫ a, ((∂μ/∂ν) a).toReal * (κ.singularPart η a .univ).toReal ∂ν
      + derivAtTop f * μ.singularPart ν .univ := by
        gcongr
        norm_cast
        exact integral_f_rnDeriv_le_integral_add μ ν κ η hf hf_cvx hf_cont h_int (fun h ↦ (h3 h).2)
  _ = ∫ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal ∂(ν ⊗ₘ η)
      + (derivAtTop f).toReal * (((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) .univ).toReal
      + derivAtTop f * μ.singularPart ν .univ := by
        simp_rw [Kernel.singularPart_eq_singularPart_measure]
        rw [integral_rnDeriv_mul_singularPart _ _ _ _ .univ, Set.univ_prod_univ]
  _ = ∫ p, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal ∂ν ⊗ₘ η
      + derivAtTop f * (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η) .univ := by
        rw [add_assoc]
        congr
        by_cases h_top : derivAtTop f = ⊤
        · simp only [h_top, EReal.toReal_top, EReal.coe_zero, zero_mul, zero_add]
          rw [Measure.singularPart_eq_zero_of_ac (h3 h_top).1, Measure.singularPart_eq_zero_of_ac]
          · simp
          · rw [Measure.absolutelyContinuous_compProd_iff]
            exact h3 h_top
        lift (derivAtTop f) to ℝ using ⟨h_top, hf_cvx.derivAtTop_ne_bot⟩ with df
        simp only [EReal.toReal_coe]
        rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _),
          ← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
        conv_rhs => rw [μ.haveLebesgueDecomposition_add ν]
        rw [Measure.compProd_add_left, add_comm, Measure.singularPart_add]
        simp only [Measure.coe_add, Pi.add_apply]
        rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        simp only [EReal.coe_add]
        norm_cast
        rw [mul_add]
        congr
        rw [singularPart_compProd]
        simp only [Measure.coe_add, Pi.add_apply]
        simp_rw [Measure.compProd_apply .univ]
        simp only [Measure.singularPart_singularPart, Set.preimage_univ]
        rw [← lintegral_add_right]
        · rw [← lintegral_one]
          congr with a
          have h : κ a .univ = 1 := by simp
          rw [← κ.rnDeriv_add_singularPart η] at h
          simp only [Kernel.coe_add, Pi.add_apply, Measure.add_toOuterMeasure,
            OuterMeasure.coe_add] at h
          exact h.symm
        · exact Kernel.measurable_coe _ .univ

lemma fDiv_fst_le [Nonempty β] [StandardBorelSpace β]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) :
    fDiv f μ.fst ν.fst ≤ fDiv f μ ν := by
  rw [← μ.disintegrate μ.condKernel, ← ν.disintegrate ν.condKernel, Measure.fst_compProd,
    Measure.fst_compProd]
  exact le_fDiv_compProd μ.fst ν.fst μ.condKernel ν.condKernel hf hf_cvx hf_cont

lemma fDiv_snd_le [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) :
    fDiv f μ.snd ν.snd ≤ fDiv f μ ν := by
  rw [← μ.fst_map_swap, ← ν.fst_map_swap]
  refine (fDiv_fst_le _ _ hf hf_cvx hf_cont).trans_eq ?_
  exact fDiv_map_measurableEmbedding MeasurableEquiv.prodComm.measurableEmbedding

lemma fDiv_comp_le_compProd [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simp_rw [Measure.comp_eq_snd_compProd]
  exact fDiv_snd_le _ _ hf hf_cvx hf_cont

/--The **Data Processing Inequality** for the f-divergence. -/
lemma fDiv_comp_right_le [Nonempty α] [StandardBorelSpace α] [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0)) :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν := by
  calc fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν)
    ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) := fDiv_comp_le_compProd μ ν κ κ hf hf_cvx hf_cont
  _ = fDiv f μ ν := fDiv_compProd_right μ ν κ hf hf_cvx

end ProbabilityTheory

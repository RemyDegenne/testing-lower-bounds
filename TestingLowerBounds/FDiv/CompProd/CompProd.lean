/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.FDiv.CompProd.EqTopIff
/-!

# f-Divergences of composition-Products

-/

open Real MeasureTheory Filter MeasurableSpace Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : DivFunction}

section Conditional

/-- Equivalence between two possible versions of the first condition for the finiteness of the
conditional f divergence, the second version is the preferred one.-/
lemma fDiv_ae_ne_top_iff [IsFiniteKernel κ] [IsFiniteKernel η] :
    (∀ᵐ a ∂μ, fDiv f (κ a) (η a) ≠ ∞)
    ↔ (∀ᵐ a ∂μ, ∫⁻ x, f ((∂κ a/∂η a) x) ∂η a ≠ ∞) ∧ (f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) := by
  simp_rw [fDiv_ne_top_iff, eventually_and, eventually_all]

/-- Equivalence between two possible versions of the second condition for the finiteness of the
conditional f divergence, the second version is the preferred one.-/
lemma integrable_fDiv_iff [CountableOrCountablyGenerated α β] [IsFiniteMeasure μ] [IsFiniteKernel κ]
    [IsFiniteKernel η]
    (h_ac : f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫⁻ x, fDiv f (κ x) (η x) ∂μ ≠ ∞ ↔ ∫⁻ a, ∫⁻ b, f ((∂κ a/∂η a) b) ∂η a ∂μ ≠ ∞ := by
  by_cases h_top : f.derivAtTop = ∞
  · classical
    rw [lintegral_congr_ae]
    filter_upwards [h_ac h_top] with a ha
    rw [fDiv_of_absolutelyContinuous ha]
  · simp_rw [fDiv]
    rw [lintegral_add_right]
    swap
    · simp_rw [← Kernel.singularPart_eq_singularPart_measure]
      exact (Kernel.measurable_coe _ .univ).const_mul _
    simp only [ne_eq, ENNReal.add_eq_top, not_or, and_iff_left_iff_imp]
    intro _
    rw [lintegral_const_mul]
    swap
    · simp_rw [← Kernel.singularPart_eq_singularPart_measure]
      exact Kernel.measurable_coe _ .univ
    refine ENNReal.mul_ne_top h_top ?_
    rw [lintegral_singularPart _ _ _ .univ]
    simp

end Conditional

lemma integral_f_rnDeriv_mul_le_integral [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (h_int : ∫⁻ p, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p) ∂(ν ⊗ₘ η) ≠ ∞)
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫⁻ x, f ((∂μ/∂ν) x * κ x .univ) ∂ν ≤ ∫⁻ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x) ∂(ν ⊗ₘ η) := by
  rw [Measure.lintegral_compProd measurable_divFunction_rnDeriv]
  exact lintegral_mono_ae (f_rnDeriv_ae_le_lintegral μ ν κ η h_int hκη)

lemma integral_f_rnDeriv_mul_withDensity_le_integral [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (h_int : ∫⁻ p, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p) ∂(ν ⊗ₘ η) ≠ ∞) :
    ∫⁻ x, f ((∂μ/∂ν) x * η.withDensity (κ.rnDeriv η) x .univ) ∂ν
      ≤ ∫⁻ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x) ∂(ν ⊗ₘ η) := by
  calc ∫⁻ x, f ((∂μ/∂ν) x * η.withDensity (κ.rnDeriv η) x .univ) ∂ν
    ≤ ∫⁻ x, f ((∂μ ⊗ₘ (η.withDensity (κ.rnDeriv η))/∂ν ⊗ₘ η) x)
      ∂(ν ⊗ₘ η) := by
        refine integral_f_rnDeriv_mul_le_integral μ ν (η.withDensity (κ.rnDeriv η))
          η ?_ ?_
        · suffices ∫⁻ p, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p) ∂ν ⊗ₘ η
              = ∫⁻ p, f ((∂μ ⊗ₘ η.withDensity (κ.rnDeriv η)/∂ν ⊗ₘ η) p) ∂ν ⊗ₘ η by
            rwa [← this]
          refine lintegral_congr_ae ?_
          filter_upwards [Measure.rnDeriv_measure_compProd_Kernel_withDensity μ ν κ η] with x hx
          rw [hx]
        · exact ae_of_all _ (fun _ ↦ Kernel.withDensity_absolutelyContinuous _ _)
  _ = ∫⁻ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x) ∂(ν ⊗ₘ η) := by
        refine lintegral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_measure_compProd_Kernel_withDensity μ ν κ η] with x hx
        rw [hx]

lemma integral_f_rnDeriv_le_integral_add [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_int : ∫⁻ p, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p) ∂(ν ⊗ₘ η) ≠ ∞)
    (h_deriv : f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫⁻ x, f ((∂μ/∂ν) x) ∂ν
      ≤ ∫⁻ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x) ∂(ν ⊗ₘ η)
        + f.derivAtTop * ∫⁻ a, (∂μ/∂ν) a * (κ.singularPart η a .univ) ∂ν := by
  suffices ∫⁻ x, f ((∂μ/∂ν) x) ∂ν
      ≤ ∫⁻ x, f ((∂μ/∂ν) x * η.withDensity (κ.rnDeriv η) x .univ) ∂ν
        + f.derivAtTop * ∫⁻ a, (∂μ/∂ν) a * κ.singularPart η a .univ ∂ν by
    refine this.trans ?_
    gcongr
    exact integral_f_rnDeriv_mul_withDensity_le_integral μ ν κ η h_int
  let κ' := η.withDensity (κ.rnDeriv η)
  have h : ∀ᵐ a ∂ν, f ((∂μ/∂ν) a)
      ≤ f ((∂μ/∂ν) a * κ' a .univ) + f.derivAtTop * (∂μ/∂ν) a * κ.singularPart η a .univ :=
    f_rnDeriv_le_add _ _ _ _ h_deriv
  refine (lintegral_mono_ae h).trans_eq ?_
  rw [lintegral_add_left]
  swap
  · exact f.continuous.measurable.comp
      ((μ.measurable_rnDeriv _).mul (Kernel.measurable_coe _ .univ))
  unfold_let κ'
  simp_rw [mul_assoc]
  rw [lintegral_const_mul]
  exact (μ.measurable_rnDeriv _).mul (Kernel.measurable_coe _ .univ)

lemma le_fDiv_compProd [CountableOrCountablyGenerated α β] (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    fDiv f μ ν ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  by_cases h_top : fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) = ∞
  · simp [h_top]
  rw [fDiv, fDiv]
  obtain h_int := (fDiv_ne_top_iff.mp h_top).1
  rw [← ne_eq, fDiv_compProd_ne_top_iff] at h_top
  obtain ⟨_, h2⟩ := h_top
  calc ∫⁻ x, f ((∂μ/∂ν) x) ∂ν + f.derivAtTop * μ.singularPart ν .univ
    ≤ ∫⁻ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x) ∂(ν ⊗ₘ η)
      + f.derivAtTop * ∫⁻ a, (∂μ/∂ν) a * κ.singularPart η a .univ ∂ν
      + f.derivAtTop * μ.singularPart ν .univ := by
        gcongr
        exact integral_f_rnDeriv_le_integral_add μ ν κ η h_int (fun h ↦ (h2 h).2)
  _ = ∫⁻ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x) ∂(ν ⊗ₘ η)
      + f.derivAtTop * ((ν.withDensity (∂μ/∂ν)) ⊗ₘ κ).singularPart (ν ⊗ₘ η) .univ
      + f.derivAtTop * μ.singularPart ν .univ := by
        simp_rw [Kernel.singularPart_eq_singularPart_measure]
        rw [lintegral_rnDeriv_mul_singularPart _ _ _ _ .univ, Set.univ_prod_univ]
  _ = ∫⁻ p, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p) ∂ν ⊗ₘ η
      + f.derivAtTop * (μ ⊗ₘ κ).singularPart (ν ⊗ₘ η) .univ := by
        rw [add_assoc]
        congr
        by_cases h_top : f.derivAtTop = ∞
        · simp only [h_top, EReal.toReal_top, EReal.coe_zero, zero_mul, zero_add]
          rw [Measure.singularPart_eq_zero_of_ac (h2 h_top).1, Measure.singularPart_eq_zero_of_ac,
            Measure.singularPart_eq_zero_of_ac]
          · simp
          · rw [Measure.absolutelyContinuous_compProd_iff]
            exact h2 h_top
          · refine Measure.absolutelyContinuous_compProd (withDensity_absolutelyContinuous _ _) ?_
            rw [ae_withDensity_iff (μ.measurable_rnDeriv ν)]
            exact Measure.ae_rnDeriv_ne_zero_imp_of_ae (h2 h_top).2
        conv_rhs => rw [μ.haveLebesgueDecomposition_add ν]
        rw [Measure.compProd_add_left, add_comm, Measure.singularPart_add]
        simp only [Measure.coe_add, Pi.add_apply]
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
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ.fst ν.fst ≤ fDiv f μ ν := by
  rw [← μ.disintegrate μ.condKernel, ← ν.disintegrate ν.condKernel, Measure.fst_compProd,
    Measure.fst_compProd]
  exact le_fDiv_compProd μ.fst ν.fst μ.condKernel ν.condKernel

lemma fDiv_snd_le [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ.snd ν.snd ≤ fDiv f μ ν := by
  rw [← μ.fst_map_swap, ← ν.fst_map_swap]
  refine (fDiv_fst_le _ _).trans_eq ?_
  exact fDiv_map_measurableEmbedding MeasurableEquiv.prodComm.measurableEmbedding

lemma fDiv_comp_le_compProd [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    fDiv f (κ ∘ₘ μ) (η ∘ₘ ν) ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  simp_rw [Measure.comp_eq_snd_compProd]
  exact fDiv_snd_le _ _

/--The **Data Processing Inequality** for the f-divergence. -/
lemma fDiv_comp_right_le [Nonempty α] [StandardBorelSpace α] [CountableOrCountablyGenerated α β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν := by
  calc fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν)
    ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) := fDiv_comp_le_compProd μ ν κ κ
  _ = fDiv f μ ν := fDiv_compProd_right μ ν κ

end ProbabilityTheory

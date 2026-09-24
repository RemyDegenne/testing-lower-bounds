/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import TestingLowerBounds.FDiv.Basic
public import TestingLowerBounds.CompProd

/-!
# f-Divergences of composition-products

## Main statements

* `fDiv_compProd_left`: `fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = fDiv f μ ν` for a Markov kernel `κ`.
* `fDiv_prod_left`: `fDiv f (μ.prod ξ) (ν.prod ξ) = fDiv f μ ν` for a probability measure `ξ`.
* `fDiv_compProd_ne_top_iff`: finiteness of `fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η)`.
* `le_fDiv_compProd`, `fDiv_fst_le`, `fDiv_snd_le`, `fDiv_comp_le_compProd`, `fDiv_comp_right_le`:
  data processing inequalities, proved through the disintegration of the composition-product.
  They need assumptions on the measurable spaces (`CountableOrCountablyGenerated`,
  `StandardBorelSpace`). Versions without those assumptions are in
  `TestingLowerBounds.FDiv.DPIJensen`.

-/

@[expose] public section

open Real MeasureTheory Filter MeasurableSpace Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β} {f g : DivFunction}

@[simp]
lemma fDiv_compProd_left (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) = fDiv f μ ν := by
  refine fDiv_congr_measure ?_ ?_
  · have h_eq : (fun x ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ κ) x))
        =ᵐ[ν ⊗ₘ κ] fun x ↦ f ((∂μ/∂ν) x.1) := by
      filter_upwards [rnDeriv_measure_compProd_left μ ν κ] with x hx
      rw [hx]
    rw [lintegral_congr_ae h_eq, Measure.lintegral_compProd]
    · simp
    · exact measurable_divFunction_rnDeriv.comp measurable_fst
  · rw [singularPart_compProd_left, Measure.compProd_apply_univ]

/-- The f-divergence is invariant under taking the product with a probability measure. -/
lemma fDiv_prod_left (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ξ : Measure β) [IsProbabilityMeasure ξ] :
    fDiv f (μ.prod ξ) (ν.prod ξ) = fDiv f μ ν := by
  simpa [Measure.compProd_const] using fDiv_compProd_left (f := f) μ ν (Kernel.const α ξ)

section CountableOrCountablyGenerated

variable [CountableOrCountablyGenerated α β]

lemma fDiv_compProd_ne_top_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
    fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) ≠ ∞ ↔
      ∫⁻ a, ∫⁻ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b) ∂(η a) ∂ν ≠ ∞
        ∧ (f.derivAtTop = ∞ → μ ≪ ν ∧ ∀ᵐ a ∂μ, κ a ≪ η a) := by
  rw [fDiv_ne_top_iff, Measure.absolutelyContinuous_compProd_iff,
    Measure.absolutelyContinuous_compProd_right_iff,
    Measure.lintegral_compProd measurable_divFunction_rnDeriv]
  suffices ∫⁻ a, ∫⁻ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)) ∂η a ∂ν
      = ∫⁻ a, ∫⁻ b, f ((∂μ/∂ν) a * (∂κ a/∂η a) b) ∂(η a) ∂ν by
    rw [this]
  have h_eq := Kernel.rnDeriv_measure_compProd' μ ν κ η
  refine lintegral_congr_ae ?_
  filter_upwards [h_eq] with a ha
  refine lintegral_congr_ae ?_
  filter_upwards [ha] with b hb
  rw [hb]

lemma f_rnDeriv_le_add (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsFiniteKernel η]
    (h_deriv : f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∀ᵐ a ∂ ν, f ((∂μ/∂ν) a)
      ≤ f ((∂μ/∂ν) a * η.withDensity (κ.rnDeriv η) a .univ)
        + f.derivAtTop * ((∂μ/∂ν) a) * (κ.singularPart η a .univ) := by
  by_cases h_deriv_top : f.derivAtTop = ∞
  · simp only [h_deriv_top]
    have h_ae : ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → η.withDensity (κ.rnDeriv η) a = κ a := by
      refine Measure.ae_rnDeriv_ne_zero_imp_of_ae ν ?_
      filter_upwards [h_deriv h_deriv_top] with a ha_ac
      rw [Kernel.withDensity_rnDeriv_eq ha_ac]
    filter_upwards [h_ae] with a ha
    by_cases h0 : (∂μ/∂ν) a = 0
    · simp [h0]
    · rw [ha h0]
      simp
  refine ae_of_all _ fun a ↦ ?_
  let κ' := η.withDensity (κ.rnDeriv η)
  calc f ((∂μ/∂ν) a)
  _ ≤ f ((∂μ/∂ν) a * κ' a .univ)
        + f.derivAtTop * (∂μ/∂ν) a * (1 - κ' a .univ) := by
      refine f.le_add_derivAtTop' _ ?_
      calc κ' a .univ
      _ ≤ κ a .univ := by
          exact κ.withDensity_rnDeriv_le η a .univ
      _ = 1 := by simp
  _ = f ((∂μ/∂ν) a * κ' a .univ)
        + f.derivAtTop * (∂μ/∂ν) a * κ.singularPart η a .univ := by
      congr
      norm_cast
      unfold κ'
      refine ENNReal.sub_eq_of_eq_add (measure_ne_top _ _) ?_
      rw [← measure_univ (μ := κ a)]
      conv_lhs => rw [← κ.rnDeriv_add_singularPart η, add_comm]
      simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add]

lemma f_rnDeriv_ae_le_lintegral (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    (fun a ↦ f ((∂μ/∂ν) a * κ a .univ))
      ≤ᵐ[ν] fun a ↦ ∫⁻ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)) ∂(η a) := by
  have h_compProd := Kernel.rnDeriv_measure_compProd' μ ν κ η
  have hκη' : ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → κ a ≪ η a := Measure.ae_rnDeriv_ne_zero_imp_of_ae ν hκη
  filter_upwards [hκη', h_compProd, μ.rnDeriv_lt_top ν] with a h_ac h_eq h_lt_top
  have h_int : ∫⁻ b, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b) ∂η a = (∂μ/∂ν) a * κ a .univ := by
    rw [lintegral_congr_ae h_eq, lintegral_const_mul _ ((κ a).measurable_rnDeriv _)]
    by_cases h0 : (∂μ/∂ν) a = 0
    · simp [h0]
    · rw [Measure.lintegral_rnDeriv (h_ac h0)]
  rw [← h_int]
  refine f.map_lintegral_le
    ((Measure.measurable_rnDeriv _ _).comp measurable_prodMk_left).aemeasurable ?_
  rw [h_int]
  exact ENNReal.mul_ne_top h_lt_top.ne (measure_ne_top _ _)

lemma lintegral_f_rnDeriv_mul_le_lintegral (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫⁻ x, f ((∂μ/∂ν) x * κ x .univ) ∂ν ≤ ∫⁻ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x) ∂(ν ⊗ₘ η) := by
  rw [Measure.lintegral_compProd measurable_divFunction_rnDeriv]
  exact lintegral_mono_ae (f_rnDeriv_ae_le_lintegral μ ν κ η hκη)

lemma lintegral_f_rnDeriv_mul_withDensity_le_lintegral (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ η : Kernel α β) [IsFiniteKernel κ] [IsMarkovKernel η] :
    ∫⁻ x, f ((∂μ/∂ν) x * η.withDensity (κ.rnDeriv η) x .univ) ∂ν
      ≤ ∫⁻ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x) ∂(ν ⊗ₘ η) := by
  calc ∫⁻ x, f ((∂μ/∂ν) x * η.withDensity (κ.rnDeriv η) x .univ) ∂ν
    ≤ ∫⁻ x, f ((∂μ ⊗ₘ (η.withDensity (κ.rnDeriv η))/∂ν ⊗ₘ η) x)
      ∂(ν ⊗ₘ η) := by
        exact lintegral_f_rnDeriv_mul_le_lintegral μ ν (η.withDensity (κ.rnDeriv η)) η
          (ae_of_all _ fun _ ↦ Kernel.withDensity_absolutelyContinuous _ _)
  _ = ∫⁻ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x) ∂(ν ⊗ₘ η) := by
        refine lintegral_congr_ae ?_
        filter_upwards [rnDeriv_measure_compProd_withDensity_rnDeriv μ ν κ η] with x hx
        rw [hx]

lemma lintegral_f_rnDeriv_le_lintegral_add (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_deriv : f.derivAtTop = ∞ → ∀ᵐ a ∂μ, κ a ≪ η a) :
    ∫⁻ x, f ((∂μ/∂ν) x) ∂ν
      ≤ ∫⁻ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x) ∂(ν ⊗ₘ η)
        + f.derivAtTop * ∫⁻ a, (∂μ/∂ν) a * (κ.singularPart η a .univ) ∂ν := by
  suffices ∫⁻ x, f ((∂μ/∂ν) x) ∂ν
      ≤ ∫⁻ x, f ((∂μ/∂ν) x * η.withDensity (κ.rnDeriv η) x .univ) ∂ν
        + f.derivAtTop * ∫⁻ a, (∂μ/∂ν) a * κ.singularPart η a .univ ∂ν by
    refine this.trans ?_
    gcongr
    exact lintegral_f_rnDeriv_mul_withDensity_le_lintegral μ ν κ η
  let κ' := η.withDensity (κ.rnDeriv η)
  have h : ∀ᵐ a ∂ν, f ((∂μ/∂ν) a)
      ≤ f ((∂μ/∂ν) a * κ' a .univ) + f.derivAtTop * (∂μ/∂ν) a * κ.singularPart η a .univ :=
    f_rnDeriv_le_add _ _ _ _ h_deriv
  refine (lintegral_mono_ae h).trans_eq ?_
  rw [lintegral_add_left]
  swap
  · exact f.continuous.measurable.comp
      ((μ.measurable_rnDeriv _).mul (Kernel.measurable_coe _ .univ))
  unfold κ'
  simp_rw [mul_assoc]
  rw [lintegral_const_mul]
  exact (μ.measurable_rnDeriv _).mul (Kernel.measurable_coe _ .univ)

lemma le_fDiv_compProd (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    fDiv f μ ν ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) := by
  by_cases h_top : fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ η) = ∞
  · simp [h_top]
  rw [fDiv, fDiv]
  rw [← ne_eq, fDiv_compProd_ne_top_iff] at h_top
  obtain ⟨_, h2⟩ := h_top
  calc ∫⁻ x, f ((∂μ/∂ν) x) ∂ν + f.derivAtTop * μ.singularPart ν .univ
    ≤ ∫⁻ x, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x) ∂(ν ⊗ₘ η)
      + f.derivAtTop * ∫⁻ a, (∂μ/∂ν) a * κ.singularPart η a .univ ∂ν
      + f.derivAtTop * μ.singularPart ν .univ := by
        gcongr
        exact lintegral_f_rnDeriv_le_lintegral_add μ ν κ η (fun h ↦ (h2 h).2)
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
        · simp only [h_top]
          rw [Measure.singularPart_eq_zero_of_ac (h2 h_top).1, Measure.singularPart_eq_zero_of_ac,
            Measure.singularPart_eq_zero_of_ac]
          · simp
          · rw [Measure.absolutelyContinuous_compProd_iff,
              Measure.absolutelyContinuous_compProd_right_iff]
            exact h2 h_top
          · refine Measure.AbsolutelyContinuous.compProd (withDensity_absolutelyContinuous _ _) ?_
            rw [ae_withDensity_iff (μ.measurable_rnDeriv ν)]
            exact Measure.ae_rnDeriv_ne_zero_imp_of_ae ν (h2 h_top).2
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
          simp only [FunLike.coe_add, Pi.add_apply] at h
          exact h.symm
        · exact Kernel.measurable_coe _ .univ

end CountableOrCountablyGenerated

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
  simp_rw [← Measure.snd_compProd]
  exact fDiv_snd_le _ _

/-- The **Data Processing Inequality** for the f-divergence. -/
lemma fDiv_comp_right_le [Nonempty α] [StandardBorelSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν := by
  calc fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν)
    ≤ fDiv f (μ ⊗ₘ κ) (ν ⊗ₘ κ) := fDiv_comp_le_compProd μ ν κ κ
  _ = fDiv f μ ν := fDiv_compProd_left μ ν κ

end ProbabilityTheory

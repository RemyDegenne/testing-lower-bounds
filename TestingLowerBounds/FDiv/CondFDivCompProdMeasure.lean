/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.FDiv.CondFDiv
import TestingLowerBounds.FDiv.Measurable

/-!

# Conditional f-divergence

-/

open MeasureTheory MeasurableSpace Set Filter Real

open scoped ENNReal

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ : Measure α} {f : DivFunction}

lemma condFDiv_snd' [CountableOrCountablyGenerated β γ] {ξ : Kernel α β}
    [IsFiniteKernel ξ] {κ η : Kernel (α × β) γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    {a : α} :
    condFDiv f (κ.snd' a) (η.snd' a) (ξ a) = ∫⁻ b, (fDiv f (κ (a, b)) (η (a, b))) ∂ξ a := by
  simp [condFDiv, Kernel.snd'_apply]

lemma condFDiv_kernel_snd'_integrable_iff [CountableOrCountablyGenerated (α × β) γ]
    [IsFiniteMeasure μ] {ξ : Kernel α β}  [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ac : f.derivAtTop = ∞ → ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, κ (a, b) ≪ η (a, b)) :
    ∫⁻ a, condFDiv f (κ.snd' a) (η.snd' a) (ξ a) ∂μ ≠ ∞ ↔
      ∫⁻ a, ∫⁻ b, ∫⁻ x, f ((∂κ (a, b)/∂η (a, b)) x) ∂η (a, b) ∂ξ a ∂μ ≠ ∞ := by
  by_cases h_empty : Nonempty α
  swap; · have := not_nonempty_iff.mp h_empty; simp [Integrable.of_finite (μ := μ)]
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  simp_rw [condFDiv_eq_add]
  rw [lintegral_add_right]
  swap
  · refine Measurable.const_mul ?_ _
    refine Measurable.lintegral_kernel_prod_right ?_
    exact (Measure.measurable_coe .univ).comp (κ.measurable_singularPart η)
  simp only [Kernel.snd'_apply, ne_eq, ENNReal.add_eq_top, not_or, and_iff_left_iff_imp]
  intro
  rw [lintegral_const_mul]
  swap
  · refine Measurable.lintegral_kernel_prod_right ?_
    exact (Measure.measurable_coe .univ).comp (κ.measurable_singularPart η)
  by_cases h_deriv : f.derivAtTop = ∞
  · suffices ∫⁻ a, ∫⁻ b, ((κ (a, b)).singularPart (η (a, b))) univ ∂ξ a ∂μ = 0 by
      simp [this]
    rw [lintegral_eq_zero_iff]
    swap
    · refine Measurable.lintegral_kernel_prod_right ?_
      exact (Measure.measurable_coe .univ).comp (κ.measurable_singularPart η)
    filter_upwards [h_ac h_deriv] with x hx
    rw [Pi.zero_apply, lintegral_eq_zero_iff]
    swap
    · refine (Measure.measurable_coe .univ).comp ?_
      exact (κ.measurable_singularPart η).comp measurable_prod_mk_left
    filter_upwards [hx] with y hy
    simp only [Pi.zero_apply, Measure.measure_univ_eq_zero]
    exact Measure.singularPart_eq_zero_of_ac hy
  refine ENNReal.mul_ne_top h_deriv ?_
  rw [← lt_top_iff_ne_top]
  calc ∫⁻ a, ∫⁻ b, ((κ (a, b)).singularPart (η (a, b))) univ ∂ξ a ∂μ
    _ ≤ ∫⁻ a, ∫⁻ b, (κ (a, b)) univ ∂ξ a ∂μ :=
        lintegral_mono fun _ ↦ lintegral_mono fun _ ↦ Measure.singularPart_le _ _ _
    _ = ∫⁻ a, (ξ a) univ ∂μ := by simp
    _ ≤ ∫⁻ _, IsFiniteKernel.bound ξ ∂μ := lintegral_mono fun _ ↦ ξ.measure_le_bound  _ univ
    _ = IsFiniteKernel.bound ξ * μ univ := by simp
    _ < ∞ := ENNReal.mul_lt_top (IsFiniteKernel.bound_lt_top ξ) (by simp)

lemma condFDiv_kernel_snd'_eq_top_iff [CountableOrCountablyGenerated (α × β) γ]
    [IsFiniteMeasure μ] {ξ : Kernel α β}  [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ac : f.derivAtTop = ∞ → ∀ᵐ a ∂μ, ∀ᵐ b ∂ξ a, κ (a, b) ≪ η (a, b)) :
    ∫⁻ a, condFDiv f (κ.snd' a) (η.snd' a) (ξ a) ∂μ = ∞ ↔
      ∫⁻ a, ∫⁻ b, ∫⁻ x, f ((∂κ (a, b)/∂η (a, b)) x) ∂η (a, b) ∂ξ a ∂μ = ∞ := by
  rw [← not_iff_not]
  exact condFDiv_kernel_snd'_integrable_iff h_ac

lemma condFDiv_kernel_fst'_integrable_iff [CountableOrCountablyGenerated (α × β) γ]
    {μ : Measure β} [IsFiniteMeasure μ] {ξ : Kernel β α} [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h_ac : f.derivAtTop = ∞ → ∀ᵐ b ∂μ, ∀ᵐ a ∂ξ b, κ (a, b) ≪ η (a, b)) :
    ∫⁻ b, condFDiv f (κ.fst' b) (η.fst' b) (ξ b) ∂μ ≠ ∞ ↔
      ∫⁻ b, ∫⁻ a, ∫⁻ x, f ((∂κ (a, b)/∂η (a, b)) x) ∂η (a, b) ∂ξ b ∂μ ≠ ∞ := by
  simp_rw [← Kernel.snd'_swapRight]
  exact condFDiv_kernel_snd'_integrable_iff h_ac

lemma measurable_condFDiv_snd' [CountableOrCountablyGenerated (α × β) γ]
    {ξ : Kernel α β} [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η] :
    Measurable fun x ↦ condFDiv f (κ.snd' x) (η.snd' x) (ξ x) := by
  simp_rw [condFDiv, Kernel.snd'_apply]
  exact Measurable.lintegral_kernel_prod_right <| measurable_fDiv _ _

lemma condFDiv_compProd_meas_eq_top [CountableOrCountablyGenerated (α × β) γ] [IsFiniteMeasure μ]
    {ξ : Kernel α β} [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η] :
    condFDiv f κ η (μ ⊗ₘ ξ) = ∞
      ↔ ∫⁻ x, condFDiv f (κ.snd' x) (η.snd' x) (ξ x) ∂μ = ∞ := by
  by_cases h_empty : Nonempty α
  swap
  · have := not_nonempty_iff.mp h_empty
    simp only [condFDiv_of_isEmpty_left, ENNReal.zero_ne_top, ne_eq, not_eventually,
      Decidable.not_not, lintegral_of_isEmpty, or_false, false_iff, not_frequently]
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  rw [condFDiv_eq_top_iff]
  by_cases h_ac : f.derivAtTop = ∞ → ∀ᵐ x ∂(μ ⊗ₘ ξ), κ x ≪ η x
  · rw [condFDiv_kernel_snd'_eq_top_iff]
    swap; · exact fun h ↦
      (Measure.ae_compProd_iff (Kernel.measurableSet_absolutelyContinuous κ η)).mp (h_ac h)
    rw [Measure.lintegral_compProd]
    swap; · exact measurable_lintegral_f_rnDeriv _ _
    simp only [or_iff_left_iff_imp, and_imp]
    intro h_top h_not
    exact absurd (h_ac h_top) h_not
  push_neg at h_ac
  simp only [h_ac, not_false_eq_true, and_self, or_true, true_iff]
  suffices ∃ᵐ x ∂μ, condFDiv f (κ.snd' x) (η.snd' x) (ξ x) = ∞ by
    by_contra h_ne_top
    have h_lt_top := ae_lt_top ?_ h_ne_top
    swap; · exact measurable_condFDiv_snd'
    refine absurd h_lt_top ?_
    simp only [not_eventually, not_lt, top_le_iff]
    exact this
  simp_rw [condFDiv_eq_top_iff]
  simp only [Kernel.snd'_apply, not_eventually, frequently_or_distrib, frequently_and_distrib_left]
  rw [Measure.ae_compProd_iff (κ.measurableSet_absolutelyContinuous _)] at h_ac
  right
  convert h_ac with a
  simp

-- -- TODO: find a better name
lemma condFDiv_compProd_meas [CountableOrCountablyGenerated (α × β) γ] [IsFiniteMeasure μ]
    {ξ : Kernel α β} [IsFiniteKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η] :
    condFDiv f κ η (μ ⊗ₘ ξ) = ∫⁻ x, condFDiv f (κ.snd' x) (η.snd' x) (ξ x) ∂μ := by
  by_cases h_empty : Nonempty α
  swap
  · simp only [isEmpty_prod, not_nonempty_iff.mp h_empty, true_or, condFDiv_of_isEmpty_left,
      lintegral_of_isEmpty, EReal.coe_zero]
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  rw [condFDiv, Measure.lintegral_compProd (measurable_fDiv _ _)]
  rfl

-- can be generalized to sigma-finite
lemma Measure.ext_prod {μ ν : Measure (α × β)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ {s : Set α} {t : Set β} (_ : MeasurableSet s) (_ : MeasurableSet t),
      μ (s ×ˢ t) = ν (s ×ˢ t)) :
    μ = ν := by
  ext s hs
  apply induction_on_inter generateFrom_prod.symm isPiSystem_prod _ _ _ _ hs
  · simp
  · rintro _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    exact h ht₁ ht₂
  · intro t ht ht_eq
    simp_rw [measure_compl ht (measure_ne_top _ _), ht_eq]
    congr 1
    specialize h .univ .univ
    simpa only [univ_prod_univ, Measure.restrict_univ] using h
  · intro f' hf_disj hf_meas hf_eq
    simp_rw [measure_iUnion hf_disj hf_meas, hf_eq]

lemma _root_.MeasureTheory.Measure.compProd_assoc [IsFiniteMeasure μ]
    {ξ : Kernel α β} [IsFiniteKernel ξ] {κ : Kernel (α × β) γ} [IsFiniteKernel κ] :
    μ ⊗ₘ ξ ⊗ₘ κ = (μ ⊗ₘ (ξ ⊗ₖ κ)).map MeasurableEquiv.prodAssoc.symm := by
  simp_rw [Measure.compProd_eq_comp]
  rw [Measure.map_comp _ _ MeasurableEquiv.prodAssoc.symm.measurable, Measure.comp_assoc]
  congr 1
  ext a : 1
  rw [Kernel.comp_apply, Kernel.map_apply _ MeasurableEquiv.prodAssoc.symm.measurable,
    Kernel.prod_apply, Kernel.prod_apply, Kernel.id_apply]
  sorry

lemma condFDiv_compProd_meas' [CountableOrCountablyGenerated α (β × γ)]
    [CountableOrCountablyGenerated (α × β) γ] [IsFiniteMeasure μ]
    {ξ : Kernel α β} [IsMarkovKernel ξ]
    {κ η : Kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η] :
    condFDiv f κ η (μ ⊗ₘ ξ) = ∫⁻ x, condFDiv f (κ.snd' x) (η.snd' x) (ξ x) ∂μ := by
  by_cases h_empty : Nonempty α
  swap; · simp [not_nonempty_iff.mp h_empty]
  have := countableOrCountablyGenerated_right_of_prod_left_of_nonempty (α := α) (β := β) (γ := γ)
  rw [← fDiv_compProd_left]
  simp_rw [Measure.compProd_assoc]
  rw [fDiv_map_measurableEmbedding MeasurableEquiv.prodAssoc.symm.measurableEmbedding]
  rw [fDiv_compProd_left, condFDiv]
  simp_rw [Kernel.compProd_apply_eq_compProd_snd', fDiv_compProd_left]

end ProbabilityTheory
